/**
 * EUC Route Planner - Main Application
 * Finds quiet, low-speed-limit routes for electric unicycle riders
 */

(function () {
    'use strict';

    // ===== Configuration =====
    const ORS_BASE = 'https://api.openrouteservice.org';
    const OVERPASS_API = 'https://overpass-api.de/api/interpreter';
    const DEFAULT_ZOOM = 14;
    const EUC_AVG_SPEED_MPH = 18; // average EUC cruising speed for time estimates

    // Speed limit color scale
    const SPEED_COLORS = {
        15: '#2ecc71',
        20: '#2ecc71',
        25: '#2ecc71',
        30: '#27ae60',
        35: '#f1c40f',
        40: '#e67e22',
        45: '#e67e22',
        50: '#e74c3c',
        55: '#e74c3c',
        60: '#c0392b',
        65: '#c0392b',
        unknown: '#95a5a6'
    };

    function getSpeedColor(mph) {
        if (mph == null) return SPEED_COLORS.unknown;
        if (mph <= 25) return SPEED_COLORS[25];
        if (mph <= 30) return SPEED_COLORS[30];
        if (mph <= 35) return SPEED_COLORS[35];
        if (mph <= 45) return SPEED_COLORS[45];
        return SPEED_COLORS[55];
    }

    function getSpeedBadgeColor(mph) {
        return getSpeedColor(mph);
    }

    // ===== ORS Standard Plan Limits =====
    const RATE_LIMITS = {
        directions:   { daily: 2000, perMinute: 40 },
        autocomplete: { daily: 1000, perMinute: 100 },
        reverse:      { daily: 1000, perMinute: 100 },
        search:       { daily: 1000, perMinute: 100 }
    };

    // ===== Rate Limiter =====
    const rateLimiter = {
        // Sliding window of timestamps per endpoint
        _minuteLog: { directions: [], autocomplete: [], reverse: [], search: [] },

        // Daily counts persisted in localStorage
        _loadDaily() {
            const today = new Date().toISOString().slice(0, 10);
            const raw = localStorage.getItem('ors_usage');
            if (raw) {
                try {
                    const parsed = JSON.parse(raw);
                    if (parsed.date === today) return parsed.counts;
                } catch (e) { /* corrupt data, reset */ }
            }
            const fresh = { directions: 0, autocomplete: 0, reverse: 0, search: 0 };
            localStorage.setItem('ors_usage', JSON.stringify({ date: today, counts: fresh }));
            return fresh;
        },

        _saveDaily(counts) {
            const today = new Date().toISOString().slice(0, 10);
            localStorage.setItem('ors_usage', JSON.stringify({ date: today, counts }));
        },

        /** Returns true if the request is allowed, false if rate-limited. */
        canRequest(endpoint) {
            const limits = RATE_LIMITS[endpoint];
            if (!limits) return true;

            // Check daily limit
            const daily = this._loadDaily();
            if (daily[endpoint] >= limits.daily) return false;

            // Check per-minute limit (sliding window)
            const now = Date.now();
            const log = this._minuteLog[endpoint];
            // Prune entries older than 60s
            while (log.length > 0 && now - log[0] > 60000) log.shift();
            if (log.length >= limits.perMinute) return false;

            return true;
        },

        /** Record a successful request. */
        record(endpoint) {
            const daily = this._loadDaily();
            daily[endpoint] = (daily[endpoint] || 0) + 1;
            this._saveDaily(daily);

            this._minuteLog[endpoint].push(Date.now());
            updateUsageDisplay();
        },

        /** Get current daily counts for display. */
        getDailyCounts() {
            return this._loadDaily();
        }
    };

    // ===== State =====
    let map;
    let apiKey = '';
    let startCoords = null; // [lat, lng]
    let endCoords = null;
    let routeLayers = [];
    let speedMarkers = [];
    let startMarker = null;
    let endMarker = null;
    let activeInput = null; // which input is being geocoded
    let debounceTimer = null;
    let pickingDestOnMap = false; // true when user is picking destination on map

    // Multi-destination state
    let waypoints = []; // [{coords: [lat,lng], label: string}]
    let waypointMarkers = []; // Leaflet markers for intermediate waypoints

    // Navigation state
    let navActive = false;
    let navWatchId = null;
    let navPositionMarker = null;
    let navRouteCoords = null;
    let navSteps = null;
    let navSpeedData = null;
    let navCurrentStepIdx = 0;
    let navTotalDistanceMi = 0;
    let navCurrentSpeedMph = 0;
    let navCurrentSpeedLimit = null;
    let navLastPosition = null;
    let navLastTimestamp = null;

    // Ride tracking state
    let rideStartTime = null;
    let rideSpeedLog = [];      // array of speed readings (mph)
    let ridePositionLog = [];   // array of [lat, lng] for distance calc
    let rideTopSpeed = 0;
    let rideMaxRoadSpeed = null;

    // Manual speed limit overrides (keyed by "lat,lon" of route point)
    let manualSpeedOverrides = {};
    let pendingSpeedLimitCoordIdx = null; // index into route coords for the modal

    // Elevation & weather state
    let navElevationData = null;
    let windOverlay = null;

    // Multi-route state
    let allRoutes = []; // array of { routeData, routeCoords, speedData, elevationData, label, highSpeedPct }
    let selectedRouteIdx = 0;

    // ===== DOM Elements =====
    const $ = (sel) => document.querySelector(sel);
    const apiKeyInput = $('#api-key-input');
    const saveApiKeyBtn = $('#save-api-key');
    const startInput = $('#start-input');
    const endInput = $('#end-input');
    const useLocationBtn = $('#use-location-btn');
    const findRouteBtn = $('#find-route-btn');
    const suggestionsDropdown = $('#suggestions-dropdown');
    const loadingOverlay = $('#loading-overlay');
    const loadingText = $('#loading-text');
    const routeInfoPanel = $('#route-info');
    const speedLegend = $('#speed-legend');
    const sidebar = $('#sidebar');
    const toggleSidebarBtn = $('#toggle-sidebar');
    const closeSidebarBtn = $('#close-sidebar-btn');

    // ===== Home Address =====
    function loadHomeAddress() {
        try {
            const raw = localStorage.getItem('euc_home_address');
            return raw ? JSON.parse(raw) : null;
        } catch (e) { return null; }
    }

    function saveHomeAddress(label, coords) {
        localStorage.setItem('euc_home_address', JSON.stringify({ label, coords }));
        updateHomeDisplay();
    }

    function updateHomeDisplay() {
        const home = loadHomeAddress();
        const textEl = $('#home-address-text');
        const goBtn = $('#go-home-btn');
        if (home) {
            textEl.textContent = home.label;
            goBtn.disabled = false;
        } else {
            textEl.textContent = 'No home address set';
            goBtn.disabled = true;
        }
    }

    function setHomeAddress() {
        // Use the current start input if it's populated, otherwise use last waypoint
        if (startCoords && startInput.value.trim()) {
            saveHomeAddress(startInput.value.trim(), startCoords);
        } else if (waypoints.length > 0) {
            const lastWp = waypoints[waypoints.length - 1];
            saveHomeAddress(lastWp.label, lastWp.coords);
        } else {
            alert('Enter a start or destination address first, then tap Set Home.');
        }
    }

    function goHomeAddress() {
        const home = loadHomeAddress();
        if (!home) return;
        addWaypoint(home.coords, home.label);
    }

    // ===== Manual Speed Limit Overrides =====
    function loadManualSpeedOverrides() {
        try {
            const raw = localStorage.getItem('euc_speed_overrides');
            return raw ? JSON.parse(raw) : {};
        } catch (e) { return {}; }
    }

    function saveManualSpeedOverrides() {
        localStorage.setItem('euc_speed_overrides', JSON.stringify(manualSpeedOverrides));
    }

    // ===== Initialization =====
    function init() {
        initMap();
        loadApiKey();
        bindEvents();
        updateHomeDisplay();
        manualSpeedOverrides = loadManualSpeedOverrides();

        // On mobile, start with sidebar collapsed so map is visible
        if (window.innerWidth <= 768) {
            sidebar.classList.add('collapsed');
            toggleSidebarBtn.classList.add('collapsed');
        }
    }

    function initMap() {
        map = L.map('map', {
            zoomControl: true,
            attributionControl: true
        }).setView([39.8283, -98.5795], 5); // Center of US

        L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
            maxZoom: 19,
            attribution: '&copy; <a href="https://www.openstreetmap.org/copyright">OpenStreetMap</a> contributors'
        }).addTo(map);

        // Try to get user's location
        if (navigator.geolocation) {
            navigator.geolocation.getCurrentPosition(
                (pos) => {
                    map.setView([pos.coords.latitude, pos.coords.longitude], DEFAULT_ZOOM);
                },
                () => { /* silently ignore permission denied */ },
                { timeout: 5000 }
            );
        }
    }

    function loadApiKey() {
        const saved = localStorage.getItem('ors_api_key');
        if (saved) {
            apiKey = saved;
            apiKeyInput.value = saved;
            $('#api-key-section').style.borderColor = 'var(--accent-green)';
        }
    }

    // ===== Event Binding =====
    function bindEvents() {
        saveApiKeyBtn.addEventListener('click', saveApiKey);
        apiKeyInput.addEventListener('keydown', (e) => { if (e.key === 'Enter') saveApiKey(); });

        useLocationBtn.addEventListener('click', useCurrentLocation);

        // Add destination button
        const addDestBtn = $('#add-dest-btn');
        if (addDestBtn) {
            addDestBtn.addEventListener('click', () => {
                const val = endInput.value.trim();
                if (!val) return;
                // Try to geocode the typed text and add as waypoint
                geocodeAndAddWaypoint(val);
            });
        }

        // Pick destination on map button
        const pickDestBtn = $('#pick-dest-btn');
        if (pickDestBtn) {
            pickDestBtn.addEventListener('click', () => {
                pickingDestOnMap = true;
                // Collapse sidebar so user can tap the map
                if (!sidebar.classList.contains('collapsed')) {
                    toggleSidebar();
                }
            });
        }

        // Clear all fields button
        const clearAllBtn = $('#clear-all-btn');
        if (clearAllBtn) {
            clearAllBtn.addEventListener('click', clearAllFields);
        }

        // Home address buttons
        const setHomeBtn = $('#set-home-btn');
        if (setHomeBtn) setHomeBtn.addEventListener('click', setHomeAddress);
        const goHomeBtn = $('#go-home-btn');
        if (goHomeBtn) goHomeBtn.addEventListener('click', goHomeAddress);

        startInput.addEventListener('input', (e) => handleGeoInput(e, 'start'));
        endInput.addEventListener('input', (e) => handleGeoInput(e, 'end'));
        endInput.addEventListener('keydown', (e) => {
            if (e.key === 'Enter') {
                e.preventDefault();
                const val = endInput.value.trim();
                if (val) geocodeAndAddWaypoint(val);
            }
        });

        startInput.addEventListener('focus', () => { activeInput = 'start'; });
        endInput.addEventListener('focus', () => { activeInput = 'end'; });

        document.addEventListener('click', (e) => {
            if (!suggestionsDropdown.contains(e.target) && e.target !== startInput && e.target !== endInput) {
                suggestionsDropdown.classList.add('hidden');
            }
        });

        findRouteBtn.addEventListener('click', findRoute);

        toggleSidebarBtn.addEventListener('click', toggleSidebar);

        // Mobile close sidebar button
        if (closeSidebarBtn) {
            closeSidebarBtn.addEventListener('click', () => {
                if (!sidebar.classList.contains('collapsed')) {
                    toggleSidebar();
                }
            });
        }

        // Allow clicking on map to set start/end
        map.on('click', handleMapClick);
    }

    function saveApiKey() {
        const key = apiKeyInput.value.trim();
        if (!key) return;
        apiKey = key;
        localStorage.setItem('ors_api_key', key);
        $('#api-key-section').style.borderColor = 'var(--accent-green)';
    }

    // ===== Clear All Fields =====
    function clearAllFields() {
        startInput.value = '';
        endInput.value = '';
        startCoords = null;
        endCoords = null;
        waypoints = [];
        waypointMarkers.forEach(m => map.removeLayer(m));
        waypointMarkers = [];
        if (startMarker) { map.removeLayer(startMarker); startMarker = null; }
        if (endMarker) { map.removeLayer(endMarker); endMarker = null; }
        renderWaypointList();
        clearRoute();
        routeInfoPanel.classList.add('hidden');
        speedLegend.classList.add('hidden');
    }

    function toggleSidebar() {
        sidebar.classList.toggle('collapsed');
        toggleSidebarBtn.classList.toggle('collapsed');
        setTimeout(() => map.invalidateSize(), 350);
    }

    // ===== Geolocation =====
    function useCurrentLocation() {
        if (!navigator.geolocation) {
            alert('Geolocation is not supported by your browser.');
            return;
        }
        useLocationBtn.disabled = true;
        navigator.geolocation.getCurrentPosition(
            (pos) => {
                startCoords = [pos.coords.latitude, pos.coords.longitude];
                startInput.value = `${pos.coords.latitude.toFixed(5)}, ${pos.coords.longitude.toFixed(5)}`;
                map.setView(startCoords, DEFAULT_ZOOM);
                placeStartMarker(startCoords);
                useLocationBtn.disabled = false;
                // Reverse geocode to show address
                reverseGeocode(startCoords).then(addr => {
                    if (addr) startInput.value = addr;
                });
            },
            (err) => {
                alert('Could not get your location. Please enter an address manually.');
                useLocationBtn.disabled = false;
            },
            { enableHighAccuracy: true, timeout: 10000 }
        );
    }

    // ===== Geocoding (OpenRouteService) =====
    function handleGeoInput(e, which) {
        activeInput = which;
        const query = e.target.value.trim();
        if (query.length < 4) {
            suggestionsDropdown.classList.add('hidden');
            return;
        }

        clearTimeout(debounceTimer);
        debounceTimer = setTimeout(() => geocodeAutocomplete(query), 700);
    }

    /** Uses /geocode/autocomplete (separate 1000/day quota) for typing suggestions. */
    async function geocodeAutocomplete(query) {
        if (!apiKey) {
            suggestionsDropdown.innerHTML = '<div class="suggestion-item">Please enter your API key first</div>';
            suggestionsDropdown.classList.remove('hidden');
            return;
        }

        if (!rateLimiter.canRequest('autocomplete')) {
            showRateLimitWarning('Autocomplete rate limit reached. Please wait or type your full address and press Enter.');
            return;
        }

        try {
            const params = new URLSearchParams({
                api_key: apiKey,
                text: query,
                size: '5',
                'boundary.country': 'US'
            });

            // Use the focus point if the map is zoomed in, to improve relevance
            const center = map.getCenter();
            if (map.getZoom() >= 8) {
                params.set('focus.point.lat', center.lat.toFixed(5));
                params.set('focus.point.lon', center.lng.toFixed(5));
            }

            const resp = await fetch(`${ORS_BASE}/geocode/autocomplete?${params}`);
            if (resp.status === 429) {
                showRateLimitWarning('API rate limit exceeded. Please wait a moment.');
                return;
            }
            if (!resp.ok) throw new Error('Geocoding failed');
            rateLimiter.record('autocomplete');
            const data = await resp.json();

            if (!data.features || data.features.length === 0) {
                suggestionsDropdown.innerHTML = '<div class="suggestion-item">No results found</div>';
                suggestionsDropdown.classList.remove('hidden');
                return;
            }

            suggestionsDropdown.innerHTML = '';
            data.features.forEach(feature => {
                const div = document.createElement('div');
                div.className = 'suggestion-item';
                div.textContent = feature.properties.label;
                div.addEventListener('click', () => selectSuggestion(feature));
                suggestionsDropdown.appendChild(div);
            });
            suggestionsDropdown.classList.remove('hidden');
        } catch (err) {
            console.error('Geocode autocomplete error:', err);
        }
    }

    function selectSuggestion(feature) {
        const coords = [feature.geometry.coordinates[1], feature.geometry.coordinates[0]]; // [lat, lng]
        const label = feature.properties.label;

        if (activeInput === 'start') {
            startCoords = coords;
            startInput.value = label;
            placeStartMarker(coords);
        } else {
            // Add as waypoint instead of overwriting endCoords
            addWaypoint(coords, label);
            endInput.value = '';
        }

        suggestionsDropdown.classList.add('hidden');

        // Fit map to show all points
        fitMapToAllPoints();
    }

    async function reverseGeocode(coords) {
        if (!apiKey) return null;
        if (!rateLimiter.canRequest('reverse')) {
            console.warn('Reverse geocode rate limit reached, skipping.');
            return null;
        }
        try {
            const params = new URLSearchParams({
                api_key: apiKey,
                'point.lat': coords[0],
                'point.lon': coords[1],
                size: '1'
            });
            const resp = await fetch(`${ORS_BASE}/geocode/reverse?${params}`);
            if (resp.status === 429) {
                showRateLimitWarning('Reverse geocode rate limit hit. Try again in a moment.');
                return null;
            }
            if (!resp.ok) return null;
            rateLimiter.record('reverse');
            const data = await resp.json();
            if (data.features && data.features.length > 0) {
                return data.features[0].properties.label;
            }
        } catch (e) { /* ignore */ }
        return null;
    }

    // ===== Map Click Handling =====
    function handleMapClick(e) {
        const coords = [e.latlng.lat, e.latlng.lng];

        if (pickingDestOnMap) {
            pickingDestOnMap = false;
            const tempLabel = `${coords[0].toFixed(5)}, ${coords[1].toFixed(5)}`;
            addWaypoint(coords, tempLabel);
            reverseGeocode(coords).then(addr => {
                if (addr) {
                    // Update the label of the last added waypoint
                    const lastWp = waypoints[waypoints.length - 1];
                    if (lastWp && lastWp.coords[0] === coords[0] && lastWp.coords[1] === coords[1]) {
                        lastWp.label = addr;
                        renderWaypointList();
                    }
                }
            });
            // Re-open sidebar
            if (sidebar.classList.contains('collapsed')) {
                toggleSidebar();
            }
            return;
        }

        if (!startCoords) {
            startCoords = coords;
            placeStartMarker(coords);
            startInput.value = `${coords[0].toFixed(5)}, ${coords[1].toFixed(5)}`;
            reverseGeocode(coords).then(addr => { if (addr) startInput.value = addr; });
        } else {
            const tempLabel = `${coords[0].toFixed(5)}, ${coords[1].toFixed(5)}`;
            addWaypoint(coords, tempLabel);
            reverseGeocode(coords).then(addr => {
                if (addr) {
                    const lastWp = waypoints[waypoints.length - 1];
                    if (lastWp && lastWp.coords[0] === coords[0] && lastWp.coords[1] === coords[1]) {
                        lastWp.label = addr;
                        renderWaypointList();
                    }
                }
            });
        }
    }

    // ===== Markers =====
    function placeStartMarker(coords) {
        if (startMarker) map.removeLayer(startMarker);
        startMarker = L.marker(coords, {
            icon: L.divIcon({
                className: '',
                html: '<div class="start-marker-icon"><i class="fas fa-play"></i></div>',
                iconSize: [32, 32],
                iconAnchor: [16, 16]
            })
        }).addTo(map).bindPopup('Start Location');
    }

    function placeEndMarker(coords) {
        if (endMarker) map.removeLayer(endMarker);
        endMarker = L.marker(coords, {
            icon: L.divIcon({
                className: '',
                html: '<div class="end-marker-icon"><i class="fas fa-flag-checkered"></i></div>',
                iconSize: [32, 32],
                iconAnchor: [16, 16]
            })
        }).addTo(map).bindPopup('Destination');
    }

    // ===== Waypoint Management =====
    function addWaypoint(coords, label) {
        waypoints.push({ coords, label });
        endCoords = coords; // keep backward compat
        renderWaypointList();
        placeWaypointMarkers();
        fitMapToAllPoints();
    }

    function removeWaypoint(index) {
        waypoints.splice(index, 1);
        endCoords = waypoints.length > 0 ? waypoints[waypoints.length - 1].coords : null;
        renderWaypointList();
        placeWaypointMarkers();
        fitMapToAllPoints();
    }

    function renderWaypointList() {
        const container = $('#waypoint-list');
        if (!container) return;
        container.innerHTML = '';

        waypoints.forEach((wp, idx) => {
            const item = document.createElement('div');
            item.className = 'waypoint-item';
            item.draggable = true;
            item.dataset.index = idx;

            item.innerHTML =
                '<span class="waypoint-drag-handle"><i class="fas fa-grip-vertical"></i></span>' +
                '<span class="waypoint-num">' + (idx + 1) + '</span>' +
                '<span class="waypoint-label">' + escapeHtml(wp.label) + '</span>' +
                '<button class="waypoint-remove" data-idx="' + idx + '" title="Remove"><i class="fas fa-times"></i></button>';

            // Drag events
            item.addEventListener('dragstart', onWaypointDragStart);
            item.addEventListener('dragover', onWaypointDragOver);
            item.addEventListener('dragenter', onWaypointDragEnter);
            item.addEventListener('dragleave', onWaypointDragLeave);
            item.addEventListener('drop', onWaypointDrop);
            item.addEventListener('dragend', onWaypointDragEnd);

            // Touch drag support
            item.addEventListener('touchstart', onWaypointTouchStart, { passive: false });

            // Remove button
            item.querySelector('.waypoint-remove').addEventListener('click', (e) => {
                e.stopPropagation();
                removeWaypoint(idx);
            });

            container.appendChild(item);
        });
    }

    let dragSrcIndex = null;

    function onWaypointDragStart(e) {
        dragSrcIndex = parseInt(this.dataset.index, 10);
        this.classList.add('dragging');
        e.dataTransfer.effectAllowed = 'move';
        e.dataTransfer.setData('text/plain', dragSrcIndex);
    }

    function onWaypointDragOver(e) {
        e.preventDefault();
        e.dataTransfer.dropEffect = 'move';
    }

    function onWaypointDragEnter(e) {
        e.preventDefault();
        this.classList.add('drag-over');
    }

    function onWaypointDragLeave() {
        this.classList.remove('drag-over');
    }

    function onWaypointDrop(e) {
        e.preventDefault();
        this.classList.remove('drag-over');
        const targetIndex = parseInt(this.dataset.index, 10);
        if (dragSrcIndex == null || dragSrcIndex === targetIndex) return;

        // Reorder waypoints
        const moved = waypoints.splice(dragSrcIndex, 1)[0];
        waypoints.splice(targetIndex, 0, moved);
        endCoords = waypoints.length > 0 ? waypoints[waypoints.length - 1].coords : null;

        renderWaypointList();
        placeWaypointMarkers();
    }

    function onWaypointDragEnd() {
        this.classList.remove('dragging');
        document.querySelectorAll('.waypoint-item').forEach(el => el.classList.remove('drag-over'));
        dragSrcIndex = null;
    }

    // Touch-based drag for mobile
    let touchDragItem = null;
    let touchStartY = 0;

    function onWaypointTouchStart(e) {
        const handle = e.target.closest('.waypoint-drag-handle');
        if (!handle) return;
        e.preventDefault();
        touchDragItem = this;
        touchStartY = e.touches[0].clientY;
        dragSrcIndex = parseInt(this.dataset.index, 10);
        this.classList.add('dragging');

        const onTouchMove = (ev) => {
            ev.preventDefault();
            const touchY = ev.touches[0].clientY;
            const items = Array.from(document.querySelectorAll('.waypoint-item'));
            items.forEach(it => it.classList.remove('drag-over'));
            const target = document.elementFromPoint(ev.touches[0].clientX, touchY);
            const targetItem = target ? target.closest('.waypoint-item') : null;
            if (targetItem && targetItem !== touchDragItem) {
                targetItem.classList.add('drag-over');
            }
        };

        const onTouchEnd = (ev) => {
            document.removeEventListener('touchmove', onTouchMove);
            document.removeEventListener('touchend', onTouchEnd);
            if (!touchDragItem) return;
            touchDragItem.classList.remove('dragging');

            const touchY = ev.changedTouches[0].clientY;
            const target = document.elementFromPoint(ev.changedTouches[0].clientX, touchY);
            const targetItem = target ? target.closest('.waypoint-item') : null;
            if (targetItem && targetItem !== touchDragItem) {
                const targetIndex = parseInt(targetItem.dataset.index, 10);
                if (dragSrcIndex != null && dragSrcIndex !== targetIndex) {
                    const moved = waypoints.splice(dragSrcIndex, 1)[0];
                    waypoints.splice(targetIndex, 0, moved);
                    endCoords = waypoints.length > 0 ? waypoints[waypoints.length - 1].coords : null;
                    renderWaypointList();
                    placeWaypointMarkers();
                }
            }
            document.querySelectorAll('.waypoint-item').forEach(el => el.classList.remove('drag-over'));
            touchDragItem = null;
            dragSrcIndex = null;
        };

        document.addEventListener('touchmove', onTouchMove, { passive: false });
        document.addEventListener('touchend', onTouchEnd);
    }

    function placeWaypointMarkers() {
        // Remove old waypoint markers
        waypointMarkers.forEach(m => map.removeLayer(m));
        waypointMarkers = [];
        if (endMarker) { map.removeLayer(endMarker); endMarker = null; }

        waypoints.forEach((wp, idx) => {
            const isLast = idx === waypoints.length - 1;
            if (isLast) {
                // Last waypoint gets the destination marker
                placeEndMarker(wp.coords);
            } else {
                // Intermediate waypoints get numbered markers
                const marker = L.marker(wp.coords, {
                    icon: L.divIcon({
                        className: '',
                        html: '<div class="waypoint-marker-icon">' + (idx + 1) + '</div>',
                        iconSize: [28, 28],
                        iconAnchor: [14, 14]
                    })
                }).addTo(map).bindPopup('Stop ' + (idx + 1) + ': ' + escapeHtml(wp.label));
                waypointMarkers.push(marker);
            }
        });
    }

    function fitMapToAllPoints() {
        const points = [];
        if (startCoords) points.push(startCoords);
        waypoints.forEach(wp => points.push(wp.coords));
        if (points.length >= 2) {
            const bounds = L.latLngBounds(points);
            map.fitBounds(bounds, { padding: [60, 60] });
        } else if (points.length === 1) {
            map.setView(points[0], DEFAULT_ZOOM);
        }
    }

    async function geocodeAndAddWaypoint(query) {
        if (!apiKey) { alert('Please enter your API key first.'); return; }
        if (!rateLimiter.canRequest('search')) { alert('Search rate limit reached.'); return; }

        try {
            const params = new URLSearchParams({
                api_key: apiKey,
                text: query,
                size: '1',
                'boundary.country': 'US'
            });
            const center = map.getCenter();
            if (map.getZoom() >= 8) {
                params.set('focus.point.lat', center.lat.toFixed(5));
                params.set('focus.point.lon', center.lng.toFixed(5));
            }
            const resp = await fetch(`${ORS_BASE}/geocode/search?${params}`);
            if (!resp.ok) throw new Error('Geocoding failed');
            rateLimiter.record('search');
            const data = await resp.json();
            if (data.features && data.features.length > 0) {
                const f = data.features[0];
                const coords = [f.geometry.coordinates[1], f.geometry.coordinates[0]];
                addWaypoint(coords, f.properties.label);
                endInput.value = '';
            } else {
                alert('Address not found. Try a different search term.');
            }
        } catch (err) {
            console.error('Geocode search error:', err);
            alert('Could not geocode address.');
        }
    }

    // ===== Clear Previous Route =====
    function clearRoute() {
        routeLayers.forEach(layer => map.removeLayer(layer));
        routeLayers = [];
        speedMarkers.forEach(m => map.removeLayer(m));
        speedMarkers = [];
        if (windOverlay) { map.removeControl(windOverlay); windOverlay = null; }
        allRoutes = [];
        selectedRouteIdx = 0;
        const mapNavBtn = $('#map-start-nav-btn');
        if (mapNavBtn) mapNavBtn.classList.add('hidden');
        const batteryCard = $('#battery-card');
        if (batteryCard) batteryCard.classList.add('hidden');
    }

    // ===== Nearby Places Search (for Nav Add Stop) =====
    async function searchNearbyPlaces(lat, lng, radiusMeters) {
        radiusMeters = radiusMeters || 3000; // 3km default
        const query = `
            [out:json][timeout:15];
            (
              node["amenity"="fuel"](around:${radiusMeters},${lat},${lng});
              node["amenity"="fast_food"](around:${radiusMeters},${lat},${lng});
            );
            out body;
        `;

        try {
            const resp = await fetch(OVERPASS_API, {
                method: 'POST',
                headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
                body: 'data=' + encodeURIComponent(query)
            });
            if (!resp.ok) throw new Error('Overpass error');
            const data = await resp.json();

            const places = [];
            if (data.elements) {
                data.elements.forEach(el => {
                    if (!el.lat || !el.lon) return;
                    const name = (el.tags && el.tags.name) || (el.tags && el.tags.amenity === 'fuel' ? 'Gas Station' : 'Fast Food');
                    const type = el.tags && el.tags.amenity === 'fuel' ? 'fuel' : 'food';
                    const distKm = haversineDistance([lat, lng], [el.lat, el.lon]);
                    const distMi = distKm * 0.621371;
                    places.push({
                        name: name,
                        type: type,
                        coords: [el.lat, el.lon],
                        distMi: distMi
                    });
                });
            }

            // Sort by distance
            places.sort((a, b) => a.distMi - b.distMi);
            return places.slice(0, 10); // top 10 nearest
        } catch (err) {
            console.warn('Nearby places error:', err);
            return [];
        }
    }

    function showNearbyPanel() {
        const panel = $('#nearby-panel');
        const list = $('#nearby-list');
        if (!panel || !list) return;

        panel.classList.remove('hidden');
        list.innerHTML = '<p class="nearby-loading"><i class="fas fa-spinner fa-spin"></i> Finding nearby places...</p>';

        // Get current user position
        const pos = navLastPosition || (navRouteCoords && navRouteCoords[0]);
        if (!pos) {
            list.innerHTML = '<p class="nearby-loading">Cannot determine your location.</p>';
            return;
        }

        searchNearbyPlaces(pos[0], pos[1]).then(places => {
            if (places.length === 0) {
                list.innerHTML = '<p class="nearby-loading">No gas stations or fast food found nearby.</p>';
                return;
            }

            list.innerHTML = '';
            places.forEach(place => {
                const item = document.createElement('div');
                item.className = 'nearby-item';
                const icon = place.type === 'fuel' ? 'fa-gas-pump' : 'fa-utensils';
                const iconClass = place.type === 'fuel' ? 'fuel' : 'food';
                item.innerHTML =
                    '<span class="nearby-item-icon ' + iconClass + '"><i class="fas ' + icon + '"></i></span>' +
                    '<div class="nearby-item-info">' +
                    '<div class="nearby-item-name">' + escapeHtml(place.name) + '</div>' +
                    '<div class="nearby-item-dist">' + place.distMi.toFixed(1) + ' mi away</div>' +
                    '</div>';

                item.addEventListener('click', () => {
                    addStopDuringNav(place.coords, place.name);
                });
                list.appendChild(item);
            });
        });
    }

    function hideNearbyPanel() {
        const panel = $('#nearby-panel');
        if (panel) panel.classList.add('hidden');
    }

    function addStopDuringNav(coords, label) {
        hideNearbyPanel();

        // Insert as next waypoint after current position
        // Find the closest waypoint index to insert after
        let insertIdx = 0;
        if (navLastPosition && waypoints.length > 0) {
            let minDist = Infinity;
            waypoints.forEach((wp, i) => {
                const d = haversineDistance(navLastPosition, wp.coords);
                if (d < minDist) { minDist = d; insertIdx = i; }
            });
            // Insert before the closest upcoming waypoint
            // If the closest waypoint is behind us, insert after it
            if (insertIdx < waypoints.length - 1) {
                insertIdx = insertIdx; // insert before this one
            }
        }

        // Add the stop
        waypoints.splice(insertIdx, 0, { coords, label });
        endCoords = waypoints[waypoints.length - 1].coords;
        renderWaypointList();
        placeWaypointMarkers();

        // Re-calculate route from current position through all remaining waypoints
        if (navActive && navLastPosition) {
            stopNavigation();
            startCoords = navLastPosition;
            placeStartMarker(startCoords);
            startInput.value = 'Current Location';
            findRoute();
        }
    }

    // ===== Main Route Finding =====
    async function findRoute() {
        if (!apiKey) {
            alert('Please enter your OpenRouteService API key first.');
            return;
        }
        if (!startCoords) {
            alert('Please set a start location (click the map, use GPS, or enter an address).');
            return;
        }
        if (waypoints.length === 0) {
            alert('Please add at least one destination.');
            return;
        }
        if (!rateLimiter.canRequest('directions')) {
            alert('Directions API rate limit reached. Please wait before requesting another route.');
            return;
        }

        showLoading('Calculating EUC-friendly routes...');
        clearRoute();
        allRoutes = [];
        selectedRouteIdx = 0;

        // Reset feature panels for fresh results
        if ($('#weather-info')) $('#weather-info').classList.add('hidden');
        if ($('#elevation-profile')) $('#elevation-profile').classList.add('hidden');
        if ($('#range-estimate')) $('#range-estimate').classList.add('hidden');
        const routeTabs = $('#route-tabs');
        if (routeTabs) { routeTabs.innerHTML = ''; routeTabs.classList.add('hidden'); }

        try {
            // Step 1: Get routes from ORS (may return 1-3 alternatives)
            const routes = await fetchRoute();
            if (!routes || routes.length === 0) {
                hideLoading();
                alert('Could not find a route. Please try different locations.');
                return;
            }

            setLoadingText('Fetching speed limits for all routes...');

            // Step 2: Decode and fetch speed limits for each route
            const routePromises = routes.map(async (rd) => {
                const coords = decodePolyline(rd.geometry);
                const speeds = await fetchSpeedLimits(coords);
                return { routeData: rd, routeCoords: coords, speedData: speeds };
            });
            const processedRoutes = await Promise.all(routePromises);

            // Step 3: Calculate high-speed percentage for each route
            processedRoutes.forEach((r) => {
                const speeds = r.speedData.filter(s => s.mph != null).map(s => s.mph);
                const highSpeedCount = speeds.filter(s => s >= 40).length;
                r.highSpeedPct = speeds.length > 0 ? Math.round((highSpeedCount / speeds.length) * 100) : 0;
            });

            // Step 4: Sort — first route stays as fastest, rest sorted by lowest high-speed %
            if (processedRoutes.length > 1) {
                const fastest = processedRoutes[0];
                const alternatives = processedRoutes.slice(1).sort((a, b) => a.highSpeedPct - b.highSpeedPct);
                allRoutes = [fastest, ...alternatives];
            } else {
                allRoutes = processedRoutes;
            }

            // Label routes
            allRoutes[0].label = 'Fastest';
            for (let i = 1; i < allRoutes.length; i++) {
                allRoutes[i].label = 'Low Traffic ' + i;
            }

            setLoadingText('Fetching elevation & weather...');

            // Step 5: Fetch elevation & weather for first route (selected by default)
            const firstRoute = allRoutes[0];
            const [elevationData] = await Promise.all([
                fetchElevationData(firstRoute.routeCoords),
                fetchWeather(firstRoute.routeCoords)
            ]);
            firstRoute.elevationData = elevationData;

            setLoadingText('Drawing routes...');

            // Step 6: Draw all routes on map, highlight selected
            drawAllRoutes();

            // Step 7: Build route tabs if multiple routes
            if (allRoutes.length > 1) {
                buildRouteTabs();
            }

            // Step 8: Show info for selected route
            const sel = allRoutes[selectedRouteIdx];
            const allStepsForDisplay = sel.routeData.segments.flatMap(seg => seg.steps || []);
            showRouteInfo(sel.routeData, sel.speedData, allStepsForDisplay);
            drawElevationProfile(sel.routeCoords, sel.elevationData);
            updateRangeEstimate(sel.routeData, sel.elevationData);
            updateBatteryCard(sel.routeData, sel.elevationData);

            // Fit map to all routes
            const allCoords = allRoutes.flatMap(r => r.routeCoords);
            const bounds = L.latLngBounds(allCoords);
            map.fitBounds(bounds, { padding: [80, 80] });

            // Save to history (use last waypoint label as end label)
            const endLabel = waypoints.length > 0 ? waypoints[waypoints.length - 1].label : '';
            saveRouteToHistory(startInput.value, endLabel, startCoords, endCoords);

            // Store data for navigation (selected route)
            setNavDataFromRoute(sel);

            const navBtn = $('#start-nav-btn');
            if (navBtn) navBtn.classList.remove('hidden');

            const mapNavBtn = $('#map-start-nav-btn');
            if (mapNavBtn) mapNavBtn.classList.remove('hidden');

            speedLegend.classList.remove('hidden');
            hideLoading();

        } catch (err) {
            hideLoading();
            console.error('Route error:', err);
            alert('Error finding route: ' + err.message);
        }
    }

    function setNavDataFromRoute(routeObj) {
        navRouteCoords = routeObj.routeCoords;
        // Combine steps from all segments
        const allSteps = [];
        let totalDist = 0;
        routeObj.routeData.segments.forEach(seg => {
            if (seg.steps) allSteps.push(...seg.steps);
            totalDist += seg.distance;
        });
        navSteps = allSteps;
        navSpeedData = routeObj.speedData;
        navTotalDistanceMi = totalDist;
        navElevationData = routeObj.elevationData || null;
    }

    // Draw all routes: non-selected as faded, selected with full speed colors
    function drawAllRoutes() {
        // Clear existing route layers
        routeLayers.forEach(layer => map.removeLayer(layer));
        routeLayers = [];
        speedMarkers.forEach(m => map.removeLayer(m));
        speedMarkers = [];

        // Draw non-selected routes first (behind)
        allRoutes.forEach((r, idx) => {
            if (idx === selectedRouteIdx) return;
            const line = L.polyline(r.routeCoords, {
                color: '#5a7aa5',
                weight: 5,
                opacity: 0.35,
                dashArray: '8, 8',
                interactive: true
            }).addTo(map);

            const distMi = r.routeData.segments.reduce((s, seg) => s + seg.distance, 0).toFixed(1);
            const eucTimeMin = Math.round((distMi / EUC_AVG_SPEED_MPH) * 60);
            line.bindTooltip(r.label + ' — ' + distMi + ' mi, ~' + eucTimeMin + ' min, ' + r.highSpeedPct + '% fast roads', { sticky: true });
            line.on('click', function () { selectRoute(idx); });
            routeLayers.push(line);
        });

        // Draw selected route on top with full speed colors
        const sel = allRoutes[selectedRouteIdx];
        drawColoredRoute(sel.routeCoords, sel.speedData);
        placeSpeedSigns(sel.routeCoords, sel.speedData);
    }

    function buildRouteTabs() {
        const container = $('#route-tabs');
        if (!container) return;
        container.innerHTML = '';
        container.classList.remove('hidden');

        allRoutes.forEach((r, idx) => {
            const tab = document.createElement('button');
            tab.className = 'route-tab' + (idx === selectedRouteIdx ? ' active' : '');

            const distMi = r.routeData.segments.reduce((s, seg) => s + seg.distance, 0).toFixed(1);
            const eucTimeMin = Math.round((distMi / EUC_AVG_SPEED_MPH) * 60);
            const badgeClass = idx === 0 ? 'badge-fast' : 'badge-safe';
            const badgeText = idx === 0 ? 'Fastest' : (r.highSpeedPct + '% fast roads');

            tab.innerHTML =
                '<span class="tab-label">' + r.label + '</span>' +
                '<span class="tab-detail">' + distMi + ' mi · ~' + eucTimeMin + ' min</span>' +
                '<span class="tab-badge ' + badgeClass + '">' + badgeText + '</span>';

            tab.addEventListener('click', function () { selectRoute(idx); });
            container.appendChild(tab);
        });
    }

    async function selectRoute(idx) {
        if (idx === selectedRouteIdx) return;
        selectedRouteIdx = idx;

        const sel = allRoutes[selectedRouteIdx];

        // Fetch elevation data if not yet loaded for this route
        if (!sel.elevationData) {
            showLoading('Loading route details...');
            sel.elevationData = await fetchElevationData(sel.routeCoords);
            hideLoading();
        }

        // Redraw all routes with new selection
        drawAllRoutes();

        // Update tabs
        const tabs = document.querySelectorAll('.route-tab');
        tabs.forEach((t, i) => t.classList.toggle('active', i === idx));

        // Update info panels
        const allStepsSelect = sel.routeData.segments.flatMap(seg => seg.steps || []);
        showRouteInfo(sel.routeData, sel.speedData, allStepsSelect);
        drawElevationProfile(sel.routeCoords, sel.elevationData);
        updateRangeEstimate(sel.routeData, sel.elevationData);
        updateBatteryCard(sel.routeData, sel.elevationData);

        // Re-fetch weather for new route midpoint
        await fetchWeather(sel.routeCoords);

        // Update nav data
        setNavDataFromRoute(sel);
    }

    // ===== Fetch Route from OpenRouteService =====
    async function fetchRoute() {
        const prefCheckbox = $('#prefer-residential');
        const preferResidential = prefCheckbox ? prefCheckbox.checked : true;

        // Build coordinates array: start + all waypoints
        const coords = [[startCoords[1], startCoords[0]]]; // ORS uses [lng, lat]
        waypoints.forEach(wp => coords.push([wp.coords[1], wp.coords[0]]));

        const body = {
            coordinates: coords,
            preference: preferResidential ? 'shortest' : 'recommended',
            units: 'mi',
            language: 'en',
            instructions: true,
            geometry: true,
            options: {
                avoid_features: ['ferries', 'steps']
            }
        };

        // Only request alternatives for simple A→B routes (2 coordinates)
        if (coords.length === 2) {
            body.alternative_routes = {
                target_count: 3,
                share_factor: 0.6,
                weight_factor: 1.4
            };
        }

        // Try cycling-regular first (best for EUC), fall back to foot-walking
        const profiles = ['cycling-regular', 'foot-walking'];
        let lastError = '';

        for (const profile of profiles) {
            const resp = await fetch(`${ORS_BASE}/v2/directions/${profile}`, {
                method: 'POST',
                headers: {
                    'Authorization': apiKey,
                    'Content-Type': 'application/json; charset=utf-8',
                    'Accept': 'application/json, application/geo+json'
                },
                body: JSON.stringify(body)
            });

            if (resp.status === 429) {
                throw new Error('Directions API rate limit exceeded. Please wait a moment and try again.');
            }

            if (resp.ok) {
                rateLimiter.record('directions');
                const data = await resp.json();
                if (data.routes && data.routes.length > 0) return data.routes;
            } else {
                lastError = await resp.text();
                console.warn(`ORS ${profile} failed:`, lastError);

                // If the avoid features or alternative_routes caused the error, retry without them
                if (resp.status === 400) {
                    delete body.options;
                    delete body.alternative_routes;
                    const retryResp = await fetch(`${ORS_BASE}/v2/directions/${profile}`, {
                        method: 'POST',
                        headers: {
                            'Authorization': apiKey,
                            'Content-Type': 'application/json; charset=utf-8',
                            'Accept': 'application/json, application/geo+json'
                        },
                        body: JSON.stringify(body)
                    });
                    if (retryResp.ok) {
                        rateLimiter.record('directions');
                        const retryData = await retryResp.json();
                        if (retryData.routes && retryData.routes.length > 0) return retryData.routes;
                    } else {
                        lastError = await retryResp.text();
                        console.warn(`ORS ${profile} retry failed:`, lastError);
                    }
                }
            }
        }

        console.error('All ORS profiles failed. Last error:', lastError);
        throw new Error('Route request failed. Check your API key and locations.');
    }

    // ===== Decode ORS Polyline (encoded polyline format) =====
    function decodePolyline(encoded) {
        const coords = [];
        let index = 0, lat = 0, lng = 0;

        while (index < encoded.length) {
            let shift = 0, result = 0, byte;
            do {
                byte = encoded.charCodeAt(index++) - 63;
                result |= (byte & 0x1f) << shift;
                shift += 5;
            } while (byte >= 0x20);
            lat += (result & 1) ? ~(result >> 1) : (result >> 1);

            shift = 0; result = 0;
            do {
                byte = encoded.charCodeAt(index++) - 63;
                result |= (byte & 0x1f) << shift;
                shift += 5;
            } while (byte >= 0x20);
            lng += (result & 1) ? ~(result >> 1) : (result >> 1);

            coords.push([lat / 1e5, lng / 1e5]);
        }
        return coords;
    }

    // ===== Fetch Speed Limits from Overpass API =====
    async function fetchSpeedLimits(routeCoords) {
        // Sample points along the route (every ~20 points to avoid huge queries)
        const sampleRate = Math.max(1, Math.floor(routeCoords.length / 80));
        const sampled = routeCoords.filter((_, i) => i % sampleRate === 0 || i === routeCoords.length - 1);

        // Build bounding box
        const lats = sampled.map(c => c[0]);
        const lngs = sampled.map(c => c[1]);
        const south = Math.min(...lats) - 0.005;
        const north = Math.max(...lats) + 0.005;
        const west = Math.min(...lngs) - 0.005;
        const east = Math.max(...lngs) + 0.005;

        // Overpass query for roads with speed limits in the bounding box
        const query = `
            [out:json][timeout:30];
            way["maxspeed"](${south},${west},${north},${east});
            out body geom;
        `;

        try {
            const resp = await fetch(OVERPASS_API, {
                method: 'POST',
                headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
                body: 'data=' + encodeURIComponent(query)
            });

            if (!resp.ok) throw new Error('Overpass API error');
            const data = await resp.json();

            // Build a spatial index of road segments with speed limits
            const roads = [];
            if (data.elements) {
                data.elements.forEach(el => {
                    if (el.type === 'way' && el.tags && el.tags.maxspeed && el.geometry) {
                        const speedStr = el.tags.maxspeed;
                        const mph = parseSpeedLimit(speedStr);
                        const roadName = el.tags.name || el.tags.ref || 'Unnamed Road';
                        const roadType = el.tags.highway || 'road';
                        const geom = el.geometry.map(n => [n.lat, n.lon]);
                        roads.push({ mph, name: roadName, type: roadType, geometry: geom });
                    }
                });
            }

            // Match each route point to the nearest road with speed data
            return matchSpeedToRoute(routeCoords, roads);

        } catch (err) {
            console.warn('Speed limit fetch error:', err);
            // Return unknown speed for all points
            return routeCoords.map(() => ({ mph: null, name: 'Unknown', type: 'road' }));
        }
    }

    function parseSpeedLimit(speedStr) {
        if (!speedStr) return null;
        // Handle formats: "30 mph", "30", "50 km/h"
        const match = speedStr.match(/(\d+)/);
        if (!match) return null;
        let val = parseInt(match[1], 10);
        if (speedStr.toLowerCase().includes('km/h') || speedStr.toLowerCase().includes('kph')) {
            val = Math.round(val * 0.621371); // km/h to mph
        }
        return val;
    }

    function matchSpeedToRoute(routeCoords, roads) {
        return routeCoords.map((point, idx) => {
            // Check for manual override first
            const key = `${point[0].toFixed(4)},${point[1].toFixed(4)}`;
            if (manualSpeedOverrides[key] != null) {
                return { mph: manualSpeedOverrides[key], name: 'Manual', type: 'road' };
            }

            let bestDist = Infinity;
            let bestRoad = { mph: null, name: 'Unknown', type: 'road' };

            for (const road of roads) {
                for (const rp of road.geometry) {
                    const dist = haversineDistance(point, rp);
                    if (dist < bestDist && dist < 0.05) { // within ~50m
                        bestDist = dist;
                        bestRoad = { mph: road.mph, name: road.name, type: road.type };
                    }
                }
            }

            return bestRoad;
        });
    }

    function haversineDistance(a, b) {
        // Returns distance in km (approximate, fast)
        const R = 6371;
        const dLat = (b[0] - a[0]) * Math.PI / 180;
        const dLon = (b[1] - a[1]) * Math.PI / 180;
        const lat1 = a[0] * Math.PI / 180;
        const lat2 = b[0] * Math.PI / 180;
        const sinDLat = Math.sin(dLat / 2);
        const sinDLon = Math.sin(dLon / 2);
        const h = sinDLat * sinDLat + Math.cos(lat1) * Math.cos(lat2) * sinDLon * sinDLon;
        return R * 2 * Math.atan2(Math.sqrt(h), Math.sqrt(1 - h));
    }

    // ===== Draw Color-Coded Route =====
    function drawColoredRoute(routeCoords, speedData) {
        // Draw a base shadow line first
        const shadowLine = L.polyline(routeCoords, {
            color: '#000',
            weight: 9,
            opacity: 0.3
        }).addTo(map);
        routeLayers.push(shadowLine);

        // Draw colored segments based on speed limits
        let segStart = 0;
        for (let i = 1; i < routeCoords.length; i++) {
            const prevSpeed = speedData[i - 1] ? speedData[i - 1].mph : null;
            const currSpeed = speedData[i] ? speedData[i].mph : null;

            // When speed changes or at the end, draw the segment
            if (currSpeed !== prevSpeed || i === routeCoords.length - 1) {
                const segCoords = routeCoords.slice(segStart, i + 1);
                const color = getSpeedColor(prevSpeed);

                const line = L.polyline(segCoords, {
                    color: color,
                    weight: 6,
                    opacity: 0.9,
                    lineCap: 'round',
                    lineJoin: 'round'
                }).addTo(map);

                const speedLabel = prevSpeed != null ? `${prevSpeed} mph` : 'Speed unknown';
                const roadName = speedData[segStart] ? speedData[segStart].name : '';

                if (prevSpeed == null) {
                    // Unknown speed — offer to set it
                    const midIdx = Math.floor((segStart + i) / 2);
                    line.bindPopup(`<b>${roadName}</b><br>Speed limit: Unknown<br><button class="set-speed-popup-btn" data-idx="${midIdx}" style="margin-top:6px;padding:6px 12px;background:#4a90d9;color:#fff;border:none;border-radius:6px;cursor:pointer;font-size:13px;">Set Speed Limit</button>`);
                    line.on('popupopen', (e) => {
                        const btn = e.popup.getElement().querySelector('.set-speed-popup-btn');
                        if (btn) {
                            btn.addEventListener('click', () => {
                                map.closePopup();
                                openSpeedLimitModal(parseInt(btn.dataset.idx, 10), roadName);
                            });
                        }
                    });
                } else {
                    line.bindPopup(`<b>${roadName}</b><br>Speed limit: ${speedLabel}`);
                }

                routeLayers.push(line);
                segStart = i;
            }
        }
    }

    // ===== Place Speed Limit Signs on Map =====
    function placeSpeedSigns(routeCoords, speedData) {
        let lastSpeed = null;
        const minSpacing = 0.3; // minimum km between signs
        let lastSignCoord = null;

        for (let i = 0; i < routeCoords.length; i++) {
            const speed = speedData[i] ? speedData[i].mph : null;
            if (speed == null) continue;

            // Place a sign when speed changes
            if (speed !== lastSpeed) {
                // Check spacing
                if (lastSignCoord) {
                    const dist = haversineDistance(routeCoords[i], lastSignCoord);
                    if (dist < minSpacing) continue;
                }

                const marker = L.marker(routeCoords[i], {
                    icon: L.divIcon({
                        className: '',
                        html: `<div class="speed-limit-marker">${speed}</div>`,
                        iconSize: [36, 36],
                        iconAnchor: [18, 18]
                    })
                }).addTo(map);

                const roadName = speedData[i].name || 'Road';
                marker.bindPopup(`<b>${roadName}</b><br>Speed limit: ${speed} mph`);

                speedMarkers.push(marker);
                lastSpeed = speed;
                lastSignCoord = routeCoords[i];
            }
        }
    }

    // ===== Show Route Info Panel =====
    function showRouteInfo(routeData, speedData, steps) {
        // Sum across all segments for multi-waypoint routes
        let totalDistance = 0;
        let totalDuration = 0;
        const allSteps = [];
        routeData.segments.forEach(seg => {
            totalDistance += seg.distance;
            totalDuration += seg.duration;
            if (seg.steps) allSteps.push(...seg.steps);
        });
        const stepsToShow = allSteps.length > 0 ? allSteps : steps;

        const distDisplay = totalDistance.toFixed(1) + ' mi';
        const eucTimeMin = Math.round((totalDistance / EUC_AVG_SPEED_MPH) * 60);

        // Speed stats
        const speeds = speedData.filter(s => s.mph != null).map(s => s.mph);
        const avgSpeed = speeds.length > 0 ? Math.round(speeds.reduce((a, b) => a + b, 0) / speeds.length) : '—';
        const maxSpeed = speeds.length > 0 ? Math.max(...speeds) : '—';

        $('#route-distance').textContent = distDisplay;
        $('#route-time').textContent = `~${eucTimeMin} min`;
        $('#route-avg-speed').textContent = avgSpeed !== '—' ? `${avgSpeed} mph` : '—';
        $('#route-max-speed').textContent = maxSpeed !== '—' ? `${maxSpeed} mph` : '—';

        // Speed breakdown chart
        buildSpeedBreakdown(speedData);

        // Directions
        buildDirections(stepsToShow, speedData, routeData);

        routeInfoPanel.classList.remove('hidden');

        // On mobile, auto-collapse sidebar to show map with route
        if (window.innerWidth <= 768 && !sidebar.classList.contains('collapsed')) {
            setTimeout(() => toggleSidebar(), 600);
        }
    }

    function buildSpeedBreakdown(speedData) {
        const container = $('#speed-breakdown');
        container.innerHTML = '';

        const buckets = {
            '≤ 25 mph': { count: 0, color: '#2ecc71' },
            '30 mph': { count: 0, color: '#27ae60' },
            '35 mph': { count: 0, color: '#f1c40f' },
            '40–45 mph': { count: 0, color: '#e67e22' },
            '50+ mph': { count: 0, color: '#e74c3c' },
            'Unknown': { count: 0, color: '#95a5a6' }
        };

        speedData.forEach(s => {
            if (s.mph == null) buckets['Unknown'].count++;
            else if (s.mph <= 25) buckets['≤ 25 mph'].count++;
            else if (s.mph <= 30) buckets['30 mph'].count++;
            else if (s.mph <= 35) buckets['35 mph'].count++;
            else if (s.mph <= 45) buckets['40–45 mph'].count++;
            else buckets['50+ mph'].count++;
        });

        const total = speedData.length;

        Object.entries(buckets).forEach(([label, data]) => {
            if (data.count === 0) return;
            const pct = Math.round((data.count / total) * 100);

            const item = document.createElement('div');
            item.className = 'speed-bar-item';
            item.innerHTML = `
                <span class="speed-bar-color" style="background: ${data.color};"></span>
                <span class="speed-bar-label">${label}</span>
                <span class="speed-bar-track">
                    <span class="speed-bar-fill" style="width: ${pct}%; background: ${data.color};"></span>
                </span>
                <span class="speed-bar-pct">${pct}%</span>
            `;
            container.appendChild(item);
        });
    }

    function buildDirections(steps, speedData, routeData) {
        const container = $('#directions-list');
        container.innerHTML = '';

        steps.forEach((step, idx) => {
            // Try to find speed limit for this step's location
            // Use the waypoint indices from the step
            const waypointIdx = Math.min(step.way_points[0], speedData.length - 1);
            const speed = speedData[waypointIdx] ? speedData[waypointIdx].mph : null;

            const div = document.createElement('div');
            div.className = 'direction-step';

            const speedBadge = speed != null
                ? `<span class="direction-speed-badge" style="background: ${getSpeedBadgeColor(speed)};">${speed} mph</span>`
                : `<span class="direction-speed-badge" style="background: #95a5a6;">? mph</span>`;

            div.innerHTML = `
                <span class="direction-step-num">${idx + 1}</span>
                <span class="direction-step-text">${step.instruction} <small>(${(step.distance).toFixed(2)} mi)</small></span>
                ${speedBadge}
            `;
            container.appendChild(div);
        });
    }

    function populateNavDirections() {
        const container = $('#nav-hud-directions-list');
        if (!container || !navSteps) return;
        container.innerHTML = '';

        navSteps.forEach((step, idx) => {
            const waypointIdx = Math.min(step.way_points[0], (navSpeedData || []).length - 1);
            const speed = (navSpeedData && navSpeedData[waypointIdx]) ? navSpeedData[waypointIdx].mph : null;

            const div = document.createElement('div');
            div.className = 'direction-step';
            if (idx < navCurrentStepIdx) div.classList.add('completed-step');
            if (idx === navCurrentStepIdx) div.classList.add('active-step');

            const speedBadge = speed != null
                ? `<span class="direction-speed-badge" style="background: ${getSpeedBadgeColor(speed)};">${speed} mph</span>`
                : `<span class="direction-speed-badge" style="background: #95a5a6;">? mph</span>`;

            div.innerHTML = `
                <span class="direction-step-num">${idx + 1}</span>
                <span class="direction-step-text">${step.instruction} <small>(${(step.distance).toFixed(2)} mi)</small></span>
                ${speedBadge}
            `;
            container.appendChild(div);
        });
    }

    // ===== Speed Limit Modal =====
    function openSpeedLimitModal(routeCoordIdx, roadName) {
        pendingSpeedLimitCoordIdx = routeCoordIdx;
        const modal = $('#speed-limit-modal');
        const roadEl = $('#speed-limit-modal-road');
        if (roadEl) roadEl.textContent = roadName || 'Unknown Road';
        if (modal) modal.classList.remove('hidden');
    }

    function closeSpeedLimitModal() {
        const modal = $('#speed-limit-modal');
        if (modal) modal.classList.add('hidden');
        pendingSpeedLimitCoordIdx = null;
    }

    function applyManualSpeedLimit(mph) {
        if (pendingSpeedLimitCoordIdx == null || !navRouteCoords) {
            closeSpeedLimitModal();
            return;
        }

        // Apply to nearby route points (within ~100m of the selected point)
        const centerCoord = navRouteCoords[pendingSpeedLimitCoordIdx];
        navRouteCoords.forEach((coord, idx) => {
            const dist = haversineDistance(coord, centerCoord);
            if (dist < 0.15 && navSpeedData[idx] && navSpeedData[idx].mph == null) {
                const key = `${coord[0].toFixed(4)},${coord[1].toFixed(4)}`;
                manualSpeedOverrides[key] = mph;
                navSpeedData[idx] = { mph, name: 'Manual', type: 'road' };
            }
        });

        saveManualSpeedOverrides();
        closeSpeedLimitModal();

        // Re-draw the route with updated speed data
        clearRoute();
        drawColoredRoute(navRouteCoords, navSpeedData);
        placeSpeedSigns(navRouteCoords, navSpeedData);
        showRouteInfo({ segments: [{ distance: navTotalDistanceMi, duration: 0 }] }, navSpeedData, navSteps);
    }

    // ===== Elevation Data (Open-Meteo) =====
    async function fetchElevationData(routeCoords) {
        try {
            const sampleRate = Math.max(1, Math.floor(routeCoords.length / 80));
            const sampledIndices = [];
            for (let i = 0; i < routeCoords.length; i += sampleRate) {
                sampledIndices.push(i);
            }
            if (sampledIndices[sampledIndices.length - 1] !== routeCoords.length - 1) {
                sampledIndices.push(routeCoords.length - 1);
            }

            const lats = sampledIndices.map(i => routeCoords[i][0].toFixed(4)).join(',');
            const lngs = sampledIndices.map(i => routeCoords[i][1].toFixed(4)).join(',');

            const resp = await fetch(`https://api.open-meteo.com/v1/elevation?latitude=${lats}&longitude=${lngs}`);
            if (!resp.ok) throw new Error('Elevation API error');
            const data = await resp.json();

            if (!data.elevation || data.elevation.length === 0) return null;

            // Interpolate elevations for all route points (in feet)
            const elevations = new Array(routeCoords.length);
            for (let si = 0; si < sampledIndices.length; si++) {
                elevations[sampledIndices[si]] = data.elevation[si] * 3.28084; // m to ft
            }

            for (let i = 0; i < routeCoords.length; i++) {
                if (elevations[i] != null) continue;
                let prevIdx = i - 1;
                while (prevIdx >= 0 && elevations[prevIdx] == null) prevIdx--;
                let nextIdx = i + 1;
                while (nextIdx < routeCoords.length && elevations[nextIdx] == null) nextIdx++;

                if (prevIdx >= 0 && nextIdx < routeCoords.length) {
                    const t = (i - prevIdx) / (nextIdx - prevIdx);
                    elevations[i] = elevations[prevIdx] + t * (elevations[nextIdx] - elevations[prevIdx]);
                } else if (prevIdx >= 0) {
                    elevations[i] = elevations[prevIdx];
                } else if (nextIdx < routeCoords.length) {
                    elevations[i] = elevations[nextIdx];
                } else {
                    elevations[i] = 0;
                }
            }

            return elevations;
        } catch (e) {
            console.warn('Elevation fetch error:', e);
            return null;
        }
    }

    // ===== Draw Elevation Profile =====
    function drawElevationProfile(routeCoords, elevations) {
        const container = $('#elevation-profile');
        const canvas = document.getElementById('elevation-canvas');
        if (!container || !canvas || !elevations || elevations.length < 2) return;

        container.classList.remove('hidden');

        const dpr = window.devicePixelRatio || 1;
        const cw = canvas.clientWidth || 300;
        const ch = 120;
        canvas.width = cw * dpr;
        canvas.height = ch * dpr;
        canvas.style.height = ch + 'px';

        const ctx = canvas.getContext('2d');
        ctx.scale(dpr, dpr);

        // Calculate cumulative distances in miles
        const distances = [0];
        for (let i = 1; i < routeCoords.length; i++) {
            distances.push(distances[i - 1] + haversineDistance(routeCoords[i - 1], routeCoords[i]) * 0.621371);
        }
        const totalDist = distances[distances.length - 1] || 1;

        const minElev = Math.min(...elevations) - 10;
        const maxElev = Math.max(...elevations) + 10;
        const elevRange = maxElev - minElev || 1;

        const pad = { top: 8, bottom: 18, left: 36, right: 6 };
        const plotW = cw - pad.left - pad.right;
        const plotH = ch - pad.top - pad.bottom;

        // Grid lines and labels
        ctx.strokeStyle = 'rgba(255,255,255,0.08)';
        ctx.lineWidth = 1;
        ctx.fillStyle = '#6b7280';
        ctx.font = '9px sans-serif';
        ctx.textAlign = 'right';

        for (let i = 0; i <= 3; i++) {
            const y = pad.top + (plotH * i / 3);
            const elev = maxElev - (elevRange * i / 3);
            ctx.beginPath();
            ctx.moveTo(pad.left, y);
            ctx.lineTo(cw - pad.right, y);
            ctx.stroke();
            ctx.fillText(Math.round(elev) + "'", pad.left - 3, y + 3);
        }

        // Area fill under curve
        ctx.beginPath();
        for (let i = 0; i < elevations.length; i++) {
            const x = pad.left + (distances[i] / totalDist) * plotW;
            const y = pad.top + plotH - ((elevations[i] - minElev) / elevRange) * plotH;
            if (i === 0) ctx.moveTo(x, y);
            else ctx.lineTo(x, y);
        }
        ctx.lineTo(pad.left + plotW, pad.top + plotH);
        ctx.lineTo(pad.left, pad.top + plotH);
        ctx.closePath();

        const gradient = ctx.createLinearGradient(0, pad.top, 0, ch);
        gradient.addColorStop(0, 'rgba(74, 144, 217, 0.4)');
        gradient.addColorStop(1, 'rgba(74, 144, 217, 0.02)');
        ctx.fillStyle = gradient;
        ctx.fill();

        // Profile line
        ctx.beginPath();
        for (let i = 0; i < elevations.length; i++) {
            const x = pad.left + (distances[i] / totalDist) * plotW;
            const y = pad.top + plotH - ((elevations[i] - minElev) / elevRange) * plotH;
            if (i === 0) ctx.moveTo(x, y);
            else ctx.lineTo(x, y);
        }
        ctx.strokeStyle = '#4a90d9';
        ctx.lineWidth = 2;
        ctx.stroke();

        // Elevation stats
        let totalGain = 0, totalLoss = 0;
        for (let i = 1; i < elevations.length; i++) {
            const diff = elevations[i] - elevations[i - 1];
            if (diff > 0) totalGain += diff;
            else totalLoss += Math.abs(diff);
        }

        const gainEl = document.getElementById('elev-gain');
        const lossEl = document.getElementById('elev-loss');
        const maxEl = document.getElementById('elev-max');
        if (gainEl) gainEl.textContent = Math.round(totalGain) + ' ft gain';
        if (lossEl) lossEl.textContent = Math.round(totalLoss) + ' ft loss';
        if (maxEl) maxEl.textContent = Math.round(Math.max(...elevations)) + ' ft max';
    }

    // ===== Range Estimator =====
    function updateRangeEstimate(routeData, elevations) {
        const rangeInput = document.getElementById('wheel-range');
        const battInput = document.getElementById('battery-pct');
        const rangeEl = $('#range-estimate');
        const indicatorEl = $('#range-indicator');

        if (!rangeInput || !battInput || !rangeEl || !indicatorEl) return;

        const wheelRange = parseFloat(rangeInput.value) || 30;
        const batteryPct = Math.min(100, Math.max(1, parseFloat(battInput.value) || 100));
        const availableRange = wheelRange * (batteryPct / 100);
        const routeDistance = routeData.segments.reduce((s, seg) => s + seg.distance, 0); // miles

        // Elevation penalty: each 100ft of gain reduces effective range ~2%
        let elevGain = 0;
        if (elevations) {
            for (let i = 1; i < elevations.length; i++) {
                const diff = elevations[i] - elevations[i - 1];
                if (diff > 0) elevGain += diff;
            }
        }
        const elevPenalty = (elevGain / 100) * 0.02 * wheelRange;
        const effectiveRange = availableRange - elevPenalty;

        const usageRatio = routeDistance / effectiveRange;
        const margin = effectiveRange - routeDistance;

        let status, label, icon;
        if (usageRatio < 0.6) {
            status = 'green';
            label = Math.round(margin) + ' mi to spare';
            icon = 'fa-battery-full';
        } else if (usageRatio < 0.85) {
            status = 'yellow';
            label = 'Tight \u2014 ' + Math.round(margin) + ' mi margin';
            icon = 'fa-battery-half';
        } else if (margin > 0) {
            status = 'red';
            label = 'Very tight \u2014 ' + Math.round(margin) + ' mi margin';
            icon = 'fa-battery-quarter';
        } else {
            status = 'red';
            label = Math.round(Math.abs(margin)) + ' mi short!';
            icon = 'fa-battery-empty';
        }

        indicatorEl.className = 'range-indicator range-' + status;
        indicatorEl.innerHTML = '<i class="fas ' + icon + '"></i> <span>' + label + '</span>';
        rangeEl.classList.remove('hidden');
    }

    // ===== Battery Card (on-map overlay) =====
    function updateBatteryCard(routeData, elevations) {
        var card = $('#battery-card');
        if (!card) return;

        var rangeInput = document.getElementById('wheel-range');
        var battInput = document.getElementById('battery-pct');
        if (!rangeInput || !battInput) return;

        var wheelRange = parseFloat(rangeInput.value) || 30;
        var batteryPct = Math.min(100, Math.max(1, parseFloat(battInput.value) || 100));
        var availableRange = wheelRange * (batteryPct / 100);
        var routeDistance = routeData.segments.reduce(function(s, seg) { return s + seg.distance; }, 0); // miles

        // Elevation penalty
        var elevGain = 0;
        if (elevations) {
            for (var i = 1; i < elevations.length; i++) {
                var diff = elevations[i] - elevations[i - 1];
                if (diff > 0) elevGain += diff;
            }
        }
        var elevPenalty = (elevGain / 100) * 0.02 * wheelRange;
        var effectiveRange = availableRange - elevPenalty;

        // One-way usage
        var oneWayPct = Math.round((routeDistance / effectiveRange) * 100);
        var oneWayRemain = effectiveRange - routeDistance;

        // Round trip (double the distance + roughly double elevation penalty)
        var roundTripDist = routeDistance * 2;
        var roundTripEffective = effectiveRange; // same battery, double distance
        var roundTripPct = Math.round((roundTripDist / roundTripEffective) * 100);
        var roundTripRemain = roundTripEffective - roundTripDist;

        var toDestEl = $('#battery-to-dest-val');
        var roundTripEl = $('#battery-round-trip-val');
        var statusEl = $('#battery-status');

        if (toDestEl) toDestEl.textContent = Math.min(oneWayPct, 999) + '% used';
        if (roundTripEl) roundTripEl.textContent = Math.min(roundTripPct, 999) + '% used';

        // Status message
        if (statusEl) {
            if (roundTripRemain > 2) {
                statusEl.textContent = '\u2705 Round trip OK \u2014 ' + Math.round(roundTripRemain) + ' mi spare';
                statusEl.className = 'battery-card-status battery-status-good';
            } else if (oneWayRemain > 0 && roundTripRemain <= 2) {
                statusEl.textContent = '\u26A0\uFE0F Can reach dest, not enough for return';
                statusEl.className = 'battery-card-status battery-status-tight';
            } else {
                statusEl.textContent = '\u274C Cannot reach destination';
                statusEl.className = 'battery-card-status battery-status-bad';
            }
        }

        card.classList.remove('hidden');
    }

    // ===== Weather (Open-Meteo) =====
    async function fetchWeather(routeCoords) {
        try {
            const midIdx = Math.floor(routeCoords.length / 2);
            const lat = routeCoords[midIdx][0].toFixed(4);
            const lng = routeCoords[midIdx][1].toFixed(4);

            const url = 'https://api.open-meteo.com/v1/forecast?latitude=' + lat +
                '&longitude=' + lng +
                '&current=temperature_2m,relative_humidity_2m,wind_speed_10m,wind_direction_10m,wind_gusts_10m,weather_code' +
                '&temperature_unit=fahrenheit&wind_speed_unit=mph';

            const resp = await fetch(url);
            if (!resp.ok) throw new Error('Weather API error');
            const data = await resp.json();
            if (!data.current) return;

            const c = data.current;
            const temp = Math.round(c.temperature_2m);
            const windSpeed = Math.round(c.wind_speed_10m);
            const windDir = c.wind_direction_10m;
            const windGusts = Math.round(c.wind_gusts_10m || 0);
            const weatherCode = c.weather_code;
            const desc = getWeatherDescription(weatherCode);
            const windDirLabel = getWindDirectionLabel(windDir);

            const tempEl = $('#weather-temp');
            const descEl = $('#weather-desc');
            const windEl = $('#weather-wind');
            const warnEl = $('#weather-wind-warn');
            const weatherPanel = $('#weather-info');

            if (tempEl) tempEl.textContent = temp + '\u00B0F';
            if (descEl) descEl.innerHTML = '<i class="fas ' + getWeatherIcon(weatherCode) + '"></i> ' + desc;
            if (windEl) windEl.innerHTML = '<i class="fas fa-wind"></i> ' + windSpeed + ' mph ' + windDirLabel +
                (windGusts > windSpeed + 5 ? ' (gusts ' + windGusts + ')' : '');

            // Wind warnings for EUC riders
            if (warnEl) {
                if (windSpeed >= 30) {
                    warnEl.innerHTML = '<i class="fas fa-exclamation-triangle"></i> Caution: strong winds \u2014 reduced range & stability';
                    warnEl.classList.remove('hidden');
                } else if (windSpeed >= 20) {
                    warnEl.innerHTML = '<i class="fas fa-info-circle"></i> Moderate winds \u2014 may reduce range';
                    warnEl.classList.remove('hidden');
                } else {
                    warnEl.classList.add('hidden');
                }
            }

            if (weatherPanel) weatherPanel.classList.remove('hidden');

            // Add wind direction overlay on map
            addWindOverlay(windSpeed, windDir, windDirLabel);

        } catch (e) {
            console.warn('Weather fetch error:', e);
        }
    }

    function getWeatherDescription(code) {
        var codes = {
            0: 'Clear sky', 1: 'Mainly clear', 2: 'Partly cloudy', 3: 'Overcast',
            45: 'Foggy', 48: 'Rime fog',
            51: 'Light drizzle', 53: 'Mod. drizzle', 55: 'Dense drizzle',
            61: 'Light rain', 63: 'Moderate rain', 65: 'Heavy rain',
            66: 'Freezing rain', 67: 'Heavy freezing rain',
            71: 'Light snow', 73: 'Moderate snow', 75: 'Heavy snow',
            77: 'Snow grains', 80: 'Light showers', 81: 'Mod. showers', 82: 'Heavy showers',
            85: 'Light snow showers', 86: 'Heavy snow showers',
            95: 'Thunderstorm', 96: 'T-storm w/ hail', 99: 'T-storm w/ heavy hail'
        };
        return codes[code] || 'Unknown';
    }

    function getWeatherIcon(code) {
        if (code === 0) return 'fa-sun';
        if (code <= 2) return 'fa-cloud-sun';
        if (code === 3) return 'fa-cloud';
        if (code <= 48) return 'fa-smog';
        if (code <= 55) return 'fa-cloud-rain';
        if (code <= 67) return 'fa-cloud-showers-heavy';
        if (code <= 77) return 'fa-snowflake';
        if (code <= 82) return 'fa-cloud-showers-heavy';
        if (code <= 86) return 'fa-snowflake';
        return 'fa-bolt';
    }

    function getWindDirectionLabel(degrees) {
        var dirs = ['N', 'NNE', 'NE', 'ENE', 'E', 'ESE', 'SE', 'SSE',
                    'S', 'SSW', 'SW', 'WSW', 'W', 'WNW', 'NW', 'NNW'];
        return dirs[Math.round(degrees / 22.5) % 16];
    }

    function addWindOverlay(speed, direction, dirLabel) {
        if (windOverlay) { map.removeControl(windOverlay); windOverlay = null; }

        var arrowRotation = (direction + 180) % 360;

        windOverlay = L.control({ position: 'bottomleft' });
        windOverlay.onAdd = function () {
            var div = L.DomUtil.create('div', 'wind-overlay');
            div.innerHTML =
                '<div class="wind-arrow" style="transform: rotate(' + arrowRotation + 'deg);">' +
                '<i class="fas fa-arrow-up"></i></div>' +
                '<div class="wind-info">' +
                '<span class="wind-speed">' + speed + ' mph</span>' +
                '<span class="wind-dir">from ' + dirLabel + '</span></div>';
            L.DomEvent.disableClickPropagation(div);
            return div;
        };
        windOverlay.addTo(map);
    }

    // ===== Loading UI =====
    function showLoading(text) {
        loadingText.textContent = text || 'Loading...';
        loadingOverlay.classList.remove('hidden');
        findRouteBtn.disabled = true;
    }

    function setLoadingText(text) {
        loadingText.textContent = text;
    }

    function hideLoading() {
        loadingOverlay.classList.add('hidden');
        findRouteBtn.disabled = false;
    }

    // ===== Route History =====
    const MAX_SAVED_ROUTES = 10;

    function loadRouteHistory() {
        try {
            const raw = localStorage.getItem('euc_route_history');
            return raw ? JSON.parse(raw) : [];
        } catch (e) { return []; }
    }

    function saveRouteToHistory(startLabel, endLabel, startC, endC) {
        const history = loadRouteHistory();

        // Don't save duplicates (same start+end text)
        const isDuplicate = history.some(
            r => r.startLabel === startLabel && r.endLabel === endLabel
        );
        if (isDuplicate) return;

        history.unshift({
            startLabel,
            endLabel,
            startCoords: startC,
            endCoords: endC,
            timestamp: Date.now()
        });

        // Keep only the most recent routes
        if (history.length > MAX_SAVED_ROUTES) history.length = MAX_SAVED_ROUTES;

        localStorage.setItem('euc_route_history', JSON.stringify(history));
        renderRouteHistory();
    }

    function deleteRouteFromHistory(index) {
        const history = loadRouteHistory();
        history.splice(index, 1);
        localStorage.setItem('euc_route_history', JSON.stringify(history));
        renderRouteHistory();
    }

    function clearRouteHistory() {
        localStorage.removeItem('euc_route_history');
        renderRouteHistory();
    }

    function renderRouteHistory() {
        const container = $('#saved-routes-list');
        const clearBtn = $('#clear-history-btn');
        if (!container) return;

        const history = loadRouteHistory();

        if (history.length === 0) {
            container.innerHTML = '<p class="no-saved-routes">No saved routes yet. Routes are saved automatically after searching.</p>';
            if (clearBtn) clearBtn.classList.add('hidden');
            return;
        }

        if (clearBtn) clearBtn.classList.remove('hidden');
        container.innerHTML = '';

        history.forEach((route, idx) => {
            const ago = getTimeAgo(route.timestamp);
            const item = document.createElement('div');
            item.className = 'saved-route-item';
            item.title = `${route.startLabel} → ${route.endLabel}`;
            item.innerHTML = `
                <span class="saved-route-icon"><i class="fas fa-route"></i></span>
                <div class="saved-route-info">
                    <div class="saved-route-start"><i class="fas fa-circle"></i> ${escapeHtml(route.startLabel)}</div>
                    <div class="saved-route-end"><i class="fas fa-circle"></i> ${escapeHtml(route.endLabel)}</div>
                    <div class="saved-route-meta">${ago}</div>
                </div>
                <button class="saved-route-delete" title="Remove"><i class="fas fa-times"></i></button>
            `;

            // Click to load this route
            item.addEventListener('click', (e) => {
                if (e.target.closest('.saved-route-delete')) return;
                loadSavedRoute(route);
            });

            // Delete button
            item.querySelector('.saved-route-delete').addEventListener('click', (e) => {
                e.stopPropagation();
                deleteRouteFromHistory(idx);
            });

            container.appendChild(item);
        });
    }

    function loadSavedRoute(route) {
        startCoords = route.startCoords;
        startInput.value = route.startLabel;
        placeStartMarker(startCoords);

        // Clear existing waypoints and add saved destination
        waypoints = [];
        waypointMarkers.forEach(m => map.removeLayer(m));
        waypointMarkers = [];
        addWaypoint(route.endCoords, route.endLabel);
    }

    function getTimeAgo(timestamp) {
        const diff = Date.now() - timestamp;
        const mins = Math.floor(diff / 60000);
        if (mins < 1) return 'Just now';
        if (mins < 60) return `${mins}m ago`;
        const hours = Math.floor(mins / 60);
        if (hours < 24) return `${hours}h ago`;
        const days = Math.floor(hours / 24);
        return `${days}d ago`;
    }

    function escapeHtml(str) {
        const div = document.createElement('div');
        div.textContent = str;
        return div.innerHTML;
    }

    // ===== Turn-by-Turn Navigation Mode =====
    const NAV_STEP_THRESHOLD_KM = 0.04;  // ~40m to snap to current step
    const NAV_ARRIVAL_THRESHOLD_KM = 0.05; // ~50m to consider arrived
    const NAV_TURN_ICONS = {
        0: 'fa-arrow-up',         // straight
        1: 'fa-arrow-up',         // straight
        2: 'fa-arrow-left',       // sharp left
        3: 'fa-arrow-left',       // left
        4: 'fa-arrow-left',       // slight left
        5: 'fa-arrow-right',      // slight right
        6: 'fa-arrow-right',      // right
        7: 'fa-arrow-right',      // sharp right
        8: 'fa-undo',             // u-turn
        9: 'fa-flag-checkered',   // arrive
        10: 'fa-arrow-up',        // depart
        11: 'fa-circle-notch',    // roundabout
        12: 'fa-circle-notch',    // exit roundabout
    };

    function startNavigation() {
        if (!navRouteCoords || !navSteps) {
            alert('Please find a route first.');
            return;
        }
        if (!navigator.geolocation) {
            alert('Geolocation is required for navigation mode.');
            return;
        }

        navActive = true;
        navCurrentStepIdx = 0;

        // Reset ride tracking
        rideStartTime = Date.now();
        rideSpeedLog = [];
        ridePositionLog = [];
        rideTopSpeed = 0;
        rideMaxRoadSpeed = null;

        // Collapse sidebar on mobile for full map view
        if (window.innerWidth <= 768 && !sidebar.classList.contains('collapsed')) {
            toggleSidebar();
        }

        // Show navigation HUD
        const hud = $('#nav-hud');
        if (hud) {
            hud.classList.remove('hidden', 'expanded');
            hud.classList.add('entering');
            setTimeout(() => hud.classList.remove('entering'), 350);
        }

        // Hide floating map nav button
        const mapNavBtn = $('#map-start-nav-btn');
        if (mapNavBtn) mapNavBtn.classList.add('hidden');

        // Hide battery card during navigation
        const battCard = $('#battery-card');
        if (battCard) battCard.classList.add('hidden');

        // Populate directions inside the HUD panel
        populateNavDirections();

        // Hide speed legend during nav (HUD shows speed)
        speedLegend.classList.add('hidden');

        // Highlight first step
        updateNavStepHighlight();

        // Update HUD with first step info
        updateNavHUD(navSteps[0], 0);

        // Start watching GPS position
        navWatchId = navigator.geolocation.watchPosition(
            onNavPositionUpdate,
            onNavPositionError,
            {
                enableHighAccuracy: true,
                maximumAge: 2000,
                timeout: 10000
            }
        );
    }

    function stopNavigation() {
        navActive = false;
        navCurrentSpeedMph = 0;
        navCurrentSpeedLimit = null;
        navLastPosition = null;
        navLastTimestamp = null;

        if (navWatchId != null) {
            navigator.geolocation.clearWatch(navWatchId);
            navWatchId = null;
        }

        // Remove position marker
        if (navPositionMarker) {
            map.removeLayer(navPositionMarker);
            navPositionMarker = null;
        }

        // Hide HUD
        const hud = $('#nav-hud');
        if (hud) {
            hud.classList.add('hidden');
            hud.classList.remove('expanded');
        }

        // Show legend again
        speedLegend.classList.remove('hidden');

        // Remove step highlights
        document.querySelectorAll('.direction-step').forEach(el => {
            el.classList.remove('active-step', 'completed-step');
        });

        // Fit back to full route
        if (navRouteCoords && navRouteCoords.length > 0) {
            const bounds = L.latLngBounds(navRouteCoords);
            map.fitBounds(bounds, { padding: [80, 80] });
        }
    }

    function onNavPositionUpdate(position) {
        if (!navActive) return;

        const userLat = position.coords.latitude;
        const userLng = position.coords.longitude;
        const userCoord = [userLat, userLng];

        // Calculate speed from GPS
        if (position.coords.speed != null && position.coords.speed >= 0) {
            // GPS speed is in m/s, convert to mph
            navCurrentSpeedMph = Math.round(position.coords.speed * 2.23694);
        } else if (navLastPosition && navLastTimestamp) {
            // Fallback: calculate from position delta
            const distKm = haversineDistance(userCoord, navLastPosition);
            const timeSec = (position.timestamp - navLastTimestamp) / 1000;
            if (timeSec > 0.5) {
                navCurrentSpeedMph = Math.round((distKm / timeSec) * 2236.94 / 1000);
            }
        }
        navLastPosition = userCoord;
        navLastTimestamp = position.timestamp;

        // Track ride stats
        if (navCurrentSpeedMph > 0) rideSpeedLog.push(navCurrentSpeedMph);
        if (navCurrentSpeedMph > rideTopSpeed) rideTopSpeed = navCurrentSpeedMph;
        ridePositionLog.push(userCoord);

        // Track max road speed limit encountered
        if (navSpeedData && navSteps && navSteps[navCurrentStepIdx]) {
            const wpIdx = Math.min(navSteps[navCurrentStepIdx].way_points[0], navSpeedData.length - 1);
            const roadSpd = navSpeedData[wpIdx] ? navSpeedData[wpIdx].mph : null;
            if (roadSpd != null && (rideMaxRoadSpeed == null || roadSpd > rideMaxRoadSpeed)) {
                rideMaxRoadSpeed = roadSpd;
            }
        }

        // Update speedometer display
        updateSpeedometer();

        // Update / create position marker
        if (navPositionMarker) {
            navPositionMarker.setLatLng(userCoord);
        } else {
            navPositionMarker = L.marker(userCoord, {
                icon: L.divIcon({
                    className: '',
                    html: '<div class="nav-position-marker"><div class="nav-position-pulse"></div></div>',
                    iconSize: [22, 22],
                    iconAnchor: [11, 11]
                }),
                zIndexOffset: 1000
            }).addTo(map);
        }

        // Center map on user
        map.setView(userCoord, Math.max(map.getZoom(), 16));

        // Determine which step we're closest to
        findCurrentStep(userCoord);

        // Update HUD
        const step = navSteps[navCurrentStepIdx];
        if (step) {
            const stepStartIdx = step.way_points[0];
            const stepCoord = navRouteCoords[stepStartIdx];
            const distToStepKm = haversineDistance(userCoord, stepCoord);
            updateNavHUD(step, distToStepKm);
        }

        // Check arrival at destination
        const lastCoord = navRouteCoords[navRouteCoords.length - 1];
        const distToEnd = haversineDistance(userCoord, lastCoord);
        if (distToEnd < NAV_ARRIVAL_THRESHOLD_KM) {
            onNavArrival();
        }
    }

    function updateSpeedometer() {
        const speedValEl = $('#nav-speedometer-val');
        const speedometerEl = $('#nav-hud-speedometer');
        if (!speedValEl || !speedometerEl) return;

        speedValEl.textContent = navCurrentSpeedMph;

        // Get current speed limit
        if (navSpeedData && navSteps && navSteps[navCurrentStepIdx]) {
            const wpIdx = Math.min(navSteps[navCurrentStepIdx].way_points[0], navSpeedData.length - 1);
            navCurrentSpeedLimit = navSpeedData[wpIdx] ? navSpeedData[wpIdx].mph : null;
        }

        // Warning if over the speed limit
        if (navCurrentSpeedLimit != null && navCurrentSpeedMph > navCurrentSpeedLimit) {
            speedometerEl.classList.add('over-limit');
        } else {
            speedometerEl.classList.remove('over-limit');
        }
    }

    function onNavPositionError(err) {
        console.warn('Nav GPS error:', err);
        if (err.code === err.PERMISSION_DENIED) {
            alert('Location permission denied. Navigation requires GPS access.');
            stopNavigation();
        }
    }

    function findCurrentStep(userCoord) {
        // Walk through steps and find which one we're currently on
        // Skip already-passed steps
        let bestIdx = navCurrentStepIdx;
        let bestDist = Infinity;

        for (let i = navCurrentStepIdx; i < navSteps.length; i++) {
            const step = navSteps[i];
            // Check distance to the step's start waypoint
            const wpStart = step.way_points[0];
            const wpEnd = step.way_points[1];

            // Check distance to each polyline point in this step's segment
            for (let j = wpStart; j <= Math.min(wpEnd, navRouteCoords.length - 1); j++) {
                const dist = haversineDistance(userCoord, navRouteCoords[j]);
                if (dist < bestDist) {
                    bestDist = dist;
                    bestIdx = i;
                }
            }

            // Stop searching too far ahead
            if (i > navCurrentStepIdx + 3) break;
        }

        if (bestIdx !== navCurrentStepIdx) {
            navCurrentStepIdx = bestIdx;
            updateNavStepHighlight();
        }
    }

    function updateNavStepHighlight() {
        const stepEls = document.querySelectorAll('.direction-step');
        stepEls.forEach((el, idx) => {
            el.classList.remove('active-step', 'completed-step');
            if (idx < navCurrentStepIdx) {
                el.classList.add('completed-step');
            } else if (idx === navCurrentStepIdx) {
                el.classList.add('active-step');
                el.scrollIntoView({ behavior: 'smooth', block: 'nearest' });
            }
        });
    }

    function updateNavHUD(step, distToStepKm) {
        const iconEl = $('#nav-hud-icon');
        const distEl = $('#nav-hud-distance');
        const instrEl = $('#nav-hud-instruction');
        const speedEl = $('#nav-hud-speed-val');
        const etaEl = $('#nav-hud-eta');
        const remainEl = $('#nav-hud-remaining');
        const upcomingEl = $('#nav-hud-upcoming');

        // Turn icon
        const iconClass = NAV_TURN_ICONS[step.type] || 'fa-arrow-up';
        if (iconEl) iconEl.innerHTML = `<i class="fas ${iconClass}"></i>`;

        // Distance to next turn
        if (distEl) {
            const distMi = distToStepKm * 0.621371;
            if (distMi < 0.1) {
                const ft = Math.round(distMi * 5280);
                distEl.textContent = `${ft} ft`;
            } else {
                distEl.textContent = `${distMi.toFixed(1)} mi`;
            }
        }

        // Instruction text
        if (instrEl) instrEl.textContent = step.instruction;

        // Speed limit for current segment
        if (speedEl && navSpeedData) {
            const wpIdx = Math.min(step.way_points[0], navSpeedData.length - 1);
            const spd = navSpeedData[wpIdx] ? navSpeedData[wpIdx].mph : null;
            speedEl.textContent = spd != null ? spd : '—';
        }

        // Remaining distance and ETA
        let remainingMi = 0;
        for (let i = navCurrentStepIdx; i < navSteps.length; i++) {
            remainingMi += navSteps[i].distance;
        }
        if (remainEl) remainEl.textContent = `${remainingMi.toFixed(1)} mi left`;
        if (etaEl) {
            const etaMin = Math.round((remainingMi / EUC_AVG_SPEED_MPH) * 60);
            etaEl.textContent = etaMin > 0 ? `~${etaMin} min` : '< 1 min';
        }

        // Upcoming step preview
        if (upcomingEl) {
            const nextIdx = navCurrentStepIdx + 1;
            if (nextIdx < navSteps.length) {
                const next = navSteps[nextIdx];
                const nextIcon = NAV_TURN_ICONS[next.type] || 'fa-arrow-up';
                upcomingEl.innerHTML = `
                    <div class="upcoming-label">Then</div>
                    <div class="upcoming-text"><i class="fas ${nextIcon}"></i> ${escapeHtml(next.instruction)}</div>
                `;
            } else {
                upcomingEl.innerHTML = '';
            }
        }
    }

    function onNavArrival() {
        showRideSummary();
        stopNavigation();
    }

    function showRideSummary() {
        const overlay = $('#ride-summary');
        if (!overlay) return;

        const durationMs = rideStartTime ? Date.now() - rideStartTime : 0;
        const durationMin = Math.floor(durationMs / 60000);
        const durationSec = Math.floor((durationMs % 60000) / 1000);
        const durationStr = durationMin > 0 ? durationMin + 'm ' + durationSec + 's' : durationSec + 's';

        // Calculate actual distance from GPS positions
        let actualDistMi = 0;
        for (let i = 1; i < ridePositionLog.length; i++) {
            actualDistMi += haversineDistance(ridePositionLog[i - 1], ridePositionLog[i]) * 0.621371;
        }

        const avgSpeed = rideSpeedLog.length > 0
            ? Math.round(rideSpeedLog.reduce((a, b) => a + b, 0) / rideSpeedLog.length)
            : 0;

        // Elevation gain from nav data
        let elevGainFt = 0;
        if (navElevationData && navElevationData.length > 1) {
            for (let i = 1; i < navElevationData.length; i++) {
                const diff = navElevationData[i] - navElevationData[i - 1];
                if (diff > 0) elevGainFt += diff * 3.281;
            }
        }

        $('#ride-stat-distance').textContent = actualDistMi.toFixed(1) + ' mi';
        $('#ride-stat-duration').textContent = durationStr;
        $('#ride-stat-avg-speed').textContent = avgSpeed + ' mph';
        $('#ride-stat-top-speed').textContent = rideTopSpeed + ' mph';
        $('#ride-stat-elevation').textContent = Math.round(elevGainFt) + ' ft';
        $('#ride-stat-max-speed-road').textContent = rideMaxRoadSpeed != null ? rideMaxRoadSpeed + ' mph' : 'N/A';

        overlay.classList.remove('hidden');
    }

    // ===== Rate Limit Warning Toast =====
    function showRateLimitWarning(msg) {
        // Remove existing warning if any
        const existing = document.querySelector('.rate-limit-warning');
        if (existing) existing.remove();

        const toast = document.createElement('div');
        toast.className = 'rate-limit-warning';
        toast.textContent = msg;
        document.body.appendChild(toast);
        setTimeout(() => toast.remove(), 4000);
    }

    // ===== Usage Display =====
    function updateUsageDisplay() {
        const counts = rateLimiter.getDailyCounts();
        const panel = $('#api-usage');
        if (!panel) return;

        panel.classList.remove('hidden');

        const entries = [
            { id: 'usage-directions',   key: 'directions',   limit: RATE_LIMITS.directions.daily },
            { id: 'usage-autocomplete', key: 'autocomplete', limit: RATE_LIMITS.autocomplete.daily },
            { id: 'usage-reverse',      key: 'reverse',      limit: RATE_LIMITS.reverse.daily },
            { id: 'usage-search',       key: 'search',       limit: RATE_LIMITS.search.daily }
        ];

        entries.forEach(({ id, key, limit }) => {
            const el = $('#' + id);
            if (!el) return;
            const used = counts[key] || 0;
            el.textContent = `${used} / ${limit}`;

            const row = el.closest('.usage-row');
            if (row) {
                row.classList.remove('warn', 'danger');
                if (used >= limit * 0.9) row.classList.add('danger');
                else if (used >= limit * 0.7) row.classList.add('warn');
            }
        });
    }

    // ===== Start the app =====
    document.addEventListener('DOMContentLoaded', () => {
        init();
        updateUsageDisplay();
        renderRouteHistory();

        // Collapsible sidebar sections
        document.querySelectorAll('[data-collapse]').forEach(header => {
            header.addEventListener('click', () => {
                const section = header.closest('.collapsible');
                if (section) section.classList.toggle('collapsed-section');
            });
        });

        // Clear history button
        const clearHistBtn = $('#clear-history-btn');
        if (clearHistBtn) {
            clearHistBtn.addEventListener('click', () => {
                if (confirm('Clear all saved routes?')) clearRouteHistory();
            });
        }

        // Navigation buttons
        const startNavBtn = $('#start-nav-btn');
        if (startNavBtn) {
            startNavBtn.addEventListener('click', startNavigation);
        }
        const mapStartNavBtn = $('#map-start-nav-btn');
        if (mapStartNavBtn) {
            mapStartNavBtn.addEventListener('click', startNavigation);
        }
        const closeNavBtn = $('#close-nav-btn');
        if (closeNavBtn) {
            closeNavBtn.addEventListener('click', () => {
                if (confirm('End navigation?')) {
                    showRideSummary();
                    stopNavigation();
                }
            });
        }

        // Ride summary close button
        const rideSummaryClose = $('#ride-summary-close');
        if (rideSummaryClose) {
            rideSummaryClose.addEventListener('click', () => {
                $('#ride-summary').classList.add('hidden');
            });
        }

        // Nav Add Stop button + Nearby Panel
        const navAddStopBtn = $('#nav-add-stop-btn');
        if (navAddStopBtn) {
            navAddStopBtn.addEventListener('click', showNearbyPanel);
        }
        const nearbyPanelClose = $('#nearby-panel-close');
        if (nearbyPanelClose) {
            nearbyPanelClose.addEventListener('click', hideNearbyPanel);
        }
        const nearbyCustomBtn = $('#nearby-custom-btn');
        if (nearbyCustomBtn) {
            nearbyCustomBtn.addEventListener('click', () => {
                hideNearbyPanel();
                // Open sidebar for custom address entry
                if (sidebar.classList.contains('collapsed')) {
                    toggleSidebar();
                }
                endInput.focus();
            });
        }

        // Nav HUD handle: tap or drag to expand/collapse directions
        const navHud = $('#nav-hud');
        const navHandle = $('#nav-hud-handle');
        if (navHandle && navHud) {
            navHandle.addEventListener('click', () => {
                navHud.classList.toggle('expanded');
            });
        }

        // Speed limit modal
        const speedModalCancel = $('#speed-limit-modal-cancel');
        if (speedModalCancel) {
            speedModalCancel.addEventListener('click', closeSpeedLimitModal);
        }
        const speedOptions = document.querySelectorAll('.speed-option');
        speedOptions.forEach(btn => {
            btn.addEventListener('click', () => {
                const mph = parseInt(btn.dataset.speed, 10);
                applyManualSpeedLimit(mph);
            });
        });

        // Range estimator persistence and events
        const wheelRangeInput = $('#wheel-range');
        const batteryInput = $('#battery-pct');
        if (wheelRangeInput) {
            const savedRange = localStorage.getItem('euc_wheel_range');
            if (savedRange) wheelRangeInput.value = savedRange;
            wheelRangeInput.addEventListener('change', function () {
                localStorage.setItem('euc_wheel_range', wheelRangeInput.value);
                if (navElevationData && navTotalDistanceMi) {
                    updateRangeEstimate({ segments: [{ distance: navTotalDistanceMi }] }, navElevationData);
                }
            });
        }
        if (batteryInput) {
            batteryInput.addEventListener('change', function () {
                if (navElevationData && navTotalDistanceMi) {
                    updateRangeEstimate({ segments: [{ distance: navTotalDistanceMi }] }, navElevationData);
                }
            });
        }
    });
})();
