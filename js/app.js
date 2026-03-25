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

    // ===== DOM Elements =====
    const $ = (sel) => document.querySelector(sel);
    const apiKeyInput = $('#api-key-input');
    const saveApiKeyBtn = $('#save-api-key');
    const startInput = $('#start-input');
    const endInput = $('#end-input');
    const useLocationBtn = $('#use-location-btn');
    const clearEndBtn = $('#clear-end-btn');
    const findRouteBtn = $('#find-route-btn');
    const suggestionsDropdown = $('#suggestions-dropdown');
    const loadingOverlay = $('#loading-overlay');
    const loadingText = $('#loading-text');
    const routeInfoPanel = $('#route-info');
    const speedLegend = $('#speed-legend');
    const sidebar = $('#sidebar');
    const toggleSidebarBtn = $('#toggle-sidebar');

    // ===== Initialization =====
    function init() {
        initMap();
        loadApiKey();
        bindEvents();
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
        clearEndBtn.addEventListener('click', () => {
            endInput.value = '';
            endCoords = null;
        });

        startInput.addEventListener('input', (e) => handleGeoInput(e, 'start'));
        endInput.addEventListener('input', (e) => handleGeoInput(e, 'end'));

        startInput.addEventListener('focus', () => { activeInput = 'start'; });
        endInput.addEventListener('focus', () => { activeInput = 'end'; });

        document.addEventListener('click', (e) => {
            if (!suggestionsDropdown.contains(e.target) && e.target !== startInput && e.target !== endInput) {
                suggestionsDropdown.classList.add('hidden');
            }
        });

        findRouteBtn.addEventListener('click', findRoute);

        toggleSidebarBtn.addEventListener('click', toggleSidebar);

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
            endCoords = coords;
            endInput.value = label;
            placeEndMarker(coords);
        }

        suggestionsDropdown.classList.add('hidden');

        // Fit map to show both markers if both exist
        if (startCoords && endCoords) {
            const bounds = L.latLngBounds([startCoords, endCoords]);
            map.fitBounds(bounds, { padding: [60, 60] });
        } else {
            map.setView(coords, DEFAULT_ZOOM);
        }
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

        if (!startCoords) {
            startCoords = coords;
            placeStartMarker(coords);
            startInput.value = `${coords[0].toFixed(5)}, ${coords[1].toFixed(5)}`;
            reverseGeocode(coords).then(addr => { if (addr) startInput.value = addr; });
        } else if (!endCoords) {
            endCoords = coords;
            placeEndMarker(coords);
            endInput.value = `${coords[0].toFixed(5)}, ${coords[1].toFixed(5)}`;
            reverseGeocode(coords).then(addr => { if (addr) endInput.value = addr; });
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

    // ===== Clear Previous Route =====
    function clearRoute() {
        routeLayers.forEach(layer => map.removeLayer(layer));
        routeLayers = [];
        speedMarkers.forEach(m => map.removeLayer(m));
        speedMarkers = [];
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
        if (!endCoords) {
            alert('Please set a destination.');
            return;
        }
        if (!rateLimiter.canRequest('directions')) {
            alert('Directions API rate limit reached. Please wait before requesting another route.');
            return;
        }

        showLoading('Calculating EUC-friendly route...');
        clearRoute();

        try {
            // Step 1: Get route from ORS
            const routeData = await fetchRoute();
            if (!routeData) {
                hideLoading();
                alert('Could not find a route. Please try different locations.');
                return;
            }

            setLoadingText('Fetching speed limit data...');

            // Step 2: Decode the route geometry
            const routeCoords = decodePolyline(routeData.geometry);
            const steps = routeData.segments[0].steps;

            // Step 3: Fetch speed limits from Overpass API
            const speedData = await fetchSpeedLimits(routeCoords);

            setLoadingText('Drawing route with speed limits...');

            // Step 4: Draw the route with speed-colored segments
            drawColoredRoute(routeCoords, speedData);

            // Step 5: Place speed limit signs at key points
            placeSpeedSigns(routeCoords, speedData);

            // Step 6: Show route info
            showRouteInfo(routeData, speedData, steps);

            // Fit map to route
            const bounds = L.latLngBounds(routeCoords);
            map.fitBounds(bounds, { padding: [80, 80] });

            speedLegend.classList.remove('hidden');
            hideLoading();

        } catch (err) {
            hideLoading();
            console.error('Route error:', err);
            alert('Error finding route: ' + err.message);
        }
    }

    // ===== Fetch Route from OpenRouteService =====
    async function fetchRoute() {
        const avoidHighways = $('#avoid-highways').checked;
        const avoidToll = $('#avoid-toll').checked;
        const preferResidential = $('#prefer-residential').checked;

        // Build avoidance features
        const avoidFeatures = [];
        if (avoidHighways) avoidFeatures.push('highways');
        if (avoidToll) avoidFeatures.push('tollways');

        // Use cycling profile for quieter roads, or driving for road speed data
        // We use foot-walking or cycling as a base, but driving gives us road speed limits
        // Strategy: request driving-car route but avoid highways for EUC-suitable roads
        const body = {
            coordinates: [
                [startCoords[1], startCoords[0]], // ORS uses [lng, lat]
                [endCoords[1], endCoords[0]]
            ],
            preference: preferResidential ? 'shortest' : 'recommended',
            units: 'mi',
            language: 'en',
            instructions: true,
            geometry: true
        };

        if (avoidFeatures.length > 0) {
            body.options = {
                avoid_features: avoidFeatures
            };
        }

        const resp = await fetch(`${ORS_BASE}/v2/directions/cycling-regular`, {
            method: 'POST',
            headers: {
                'Authorization': apiKey,
                'Content-Type': 'application/json'
            },
            body: JSON.stringify(body)
        });

        if (resp.status === 429) {
            throw new Error('Directions API rate limit exceeded. Please wait a moment and try again.');
        }
        if (!resp.ok) {
            const errText = await resp.text();
            console.error('ORS error:', errText);
            throw new Error('Route request failed. Check your API key and locations.');
        }

        rateLimiter.record('directions');
        const data = await resp.json();
        if (!data.routes || data.routes.length === 0) return null;
        return data.routes[0];
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
        return routeCoords.map(point => {
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
                line.bindPopup(`<b>${roadName}</b><br>Speed limit: ${speedLabel}`);

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
        const segment = routeData.segments[0];
        const distanceMiles = (segment.distance * 0.000621371).toFixed(1); // meters to miles per ORS
        const durationMin = Math.round(segment.duration / 60);

        // If ORS returns distance in miles (we asked for units: mi)
        // Actually ORS returns summary in the requested unit
        const distDisplay = segment.distance < 100
            ? segment.distance.toFixed(1) + ' mi'
            : (segment.distance).toFixed(1) + ' mi';

        // Calculate time based on EUC speed
        const eucTimeMin = Math.round((segment.distance / EUC_AVG_SPEED_MPH) * 60);

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
        buildDirections(steps, speedData, routeData);

        routeInfoPanel.classList.remove('hidden');
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
    });
})();
