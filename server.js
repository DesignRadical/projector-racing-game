// server.js

const WebSocket = require('ws');
const http = require('http');
const express = require('express');
const path = require('path');
const os = require('os'); 

const PORT = process.env.PORT || 8080;
const app = express();
const server = http.createServer(app);
const wss = new WebSocket.Server({ server }); 

const clients = new Map();
let clientIdCounter = 0;
const players = new Map();

const GAME_TICK_RATE = 16; 
const ARTIFICIAL_INPUT_DELAY_MS = 0;
const ARTIFICIAL_OUTPUT_DELAY_MS = 0;

// --- Track Dimensions & Game Constants ---
const SERVER_TRACK_CANVAS_WIDTH = 1280; 
const SERVER_TRACK_CANVAS_HEIGHT = SERVER_TRACK_CANVAS_WIDTH * (9 / 16);

// --- MODIFIED: Road Thickness Increased by 25% ---
const SERVER_ROAD_THICKNESS = 75; // Was 60
const SERVER_ROAD_HALF_WIDTH = SERVER_ROAD_THICKNESS / 2; // Will be 37.5

const SERVER_TRACK_CENTER_X = SERVER_TRACK_CANVAS_WIDTH / 2;
const SERVER_TRACK_CENTER_Y = SERVER_TRACK_CANVAS_HEIGHT / 2;

// These calculations need to be precise and match host.html's logic
// Outer footprint of the track is determined by curveRadius and straightLength
// If we keep outer footprint the same, and increase roadThickness, the inner part "eats" into the center.
// The current host.html calculates curveRadius and straightLength based on canvas dimensions *after* accounting for road thickness.
// Let's ensure server does the same for consistency.

const TRACK_CURVE_RADIUS_CENTERLINE = SERVER_TRACK_CANVAS_HEIGHT * 0.30; // Centerline radius of curves
// The following straight length calculation must be identical to host.html's updateTrackParameters
const MIN_STRAIGHT_LENGTH = SERVER_TRACK_CANVAS_WIDTH * 0.2; 
const TRACK_STRAIGHT_LENGTH = Math.max(MIN_STRAIGHT_LENGTH, SERVER_TRACK_CANVAS_WIDTH - (2 * TRACK_CURVE_RADIUS_CENTERLINE) - (2 * SERVER_ROAD_HALF_WIDTH) - (SERVER_TRACK_CANVAS_WIDTH * 0.05)); 

const TRACK_FULL_WIDTH = TRACK_STRAIGHT_LENGTH + 2 * TRACK_CURVE_RADIUS_CENTERLINE;
const TRACK_OFFSET_X = (SERVER_TRACK_CANVAS_WIDTH - TRACK_FULL_WIDTH) / 2;

const TRACK_LEFT_CURVE_CENTER_X = TRACK_OFFSET_X + TRACK_CURVE_RADIUS_CENTERLINE;
const TRACK_RIGHT_CURVE_CENTER_X = TRACK_OFFSET_X + TRACK_CURVE_RADIUS_CENTERLINE + TRACK_STRAIGHT_LENGTH;
const TRACK_TOP_STRAIGHT_Y = SERVER_TRACK_CENTER_Y - TRACK_CURVE_RADIUS_CENTERLINE;
const TRACK_BOTTOM_STRAIGHT_Y = SERVER_TRACK_CENTER_Y + TRACK_CURVE_RADIUS_CENTERLINE;

// Car dimensions for better collision detection  
// Removed CAR_COLLISION_RADIUS - using visual track boundaries exactly

// Boost system constants
const BOOST_SPAWN_INTERVAL = 15000; // 15 seconds
const BOOST_SPEED_MULTIPLIER = 3.2; // Increased from 2.2 to 3.2 for much more noticeable boost effect (will show ~410 km/h)
const BOOST_DURATION = 2000; // 2 seconds (was 3000)
const BOOST_PICKUP_RADIUS = 20; // Distance to pickup boost
let boosts = new Map(); // Active boosts on track
let nextBoostId = 0;

// Boost spawn locations (only bottom-left and top-right as requested)
const BOOST_LOCATIONS = [
    // Bottom-left: left curve, bottom part
    { x: TRACK_LEFT_CURVE_CENTER_X - 25, y: TRACK_BOTTOM_STRAIGHT_Y - 20, location: 'bottom-left' },
    
    // Top-right: right curve, top part  
    { x: TRACK_RIGHT_CURVE_CENTER_X + 25, y: TRACK_TOP_STRAIGHT_Y + 20, location: 'top-right' },
];

const COLLISION_PARAMS = {
    roadHalfWidth: SERVER_ROAD_HALF_WIDTH, // Uses new thicker road
    straightMinX: TRACK_LEFT_CURVE_CENTER_X,
    straightMaxX: TRACK_RIGHT_CURVE_CENTER_X,
    // Match visual track boundaries exactly - no extra restrictions
    topStraightOuterY: TRACK_TOP_STRAIGHT_Y - SERVER_ROAD_HALF_WIDTH, // Visual track outer edge
    topStraightInnerY: TRACK_TOP_STRAIGHT_Y + SERVER_ROAD_HALF_WIDTH, // Visual track inner edge
    bottomStraightOuterY: TRACK_BOTTOM_STRAIGHT_Y + SERVER_ROAD_HALF_WIDTH, // Visual track outer edge
    bottomStraightInnerY: TRACK_BOTTOM_STRAIGHT_Y - SERVER_ROAD_HALF_WIDTH, // Visual track inner edge
    leftCurveCenterX: TRACK_LEFT_CURVE_CENTER_X,
    rightCurveCenterX: TRACK_RIGHT_CURVE_CENTER_X,
    curveCenterY: SERVER_TRACK_CENTER_Y,
    // Match visual track curve boundaries exactly
    curveOuterRadius: TRACK_CURVE_RADIUS_CENTERLINE + SERVER_ROAD_HALF_WIDTH, // Visual track outer radius
    curveInnerRadius: TRACK_CURVE_RADIUS_CENTERLINE - SERVER_ROAD_HALF_WIDTH  // Visual track inner radius
};
if (COLLISION_PARAMS.curveInnerRadius < 0) COLLISION_PARAMS.curveInnerRadius = 0; // Prevent negative inner radius

const FINISH_LINE_X = TRACK_LEFT_CURVE_CENTER_X + TRACK_STRAIGHT_LENGTH / 4;
const FINISH_LINE_Y_START_EDGE = TRACK_BOTTOM_STRAIGHT_Y - SERVER_ROAD_HALF_WIDTH; // Uses new road half width
const FINISH_LINE_Y_END_EDGE = TRACK_BOTTOM_STRAIGHT_Y + SERVER_ROAD_HALF_WIDTH;   // Uses new road half width
const LAP_DIRECTION_X = 1;

const startingPositions = [
    { x_offset: -30, y_offset: 0, angle: Math.PI / 2 }, { x_offset: -30, y_offset: -25, angle: Math.PI / 2 },
    { x_offset: -30, y_offset: 25, angle: Math.PI / 2 }, { x_offset: -60, y_offset: 0, angle: Math.PI / 2 },
    { x_offset: -60, y_offset: -25, angle: Math.PI / 2 }, { x_offset: -60, y_offset: 25, angle: Math.PI / 2 },
    { x_offset: -90, y_offset: 0, angle: Math.PI / 2 }, { x_offset: -90, y_offset: -25, angle: Math.PI / 2 },
];
let nextStartPositionIndex = 0;

// Car physics constants - no change here unless desired
const MAX_SPEED = 4.0; const MAX_REVERSE_SPEED = -1.8; const ACCELERATION = 0.08; 
const REVERSE_ACCELERATION = 0.08; const DECELERATION = 0.07; const TURN_SPEED_FACTOR = 0.05;
const DRIFT_FACTOR = 0.15; 
const WALL_SLIDE_SPEED_REDUCTION = 0.8; // Changed from 0.5 to 0.8 - now keeps 80% speed instead of 50%
const MIN_SLIDE_SPEED = 0.5; 
const WALL_NUDGE_AWAY_FORCE = 0.003; // Reduced from 0.008 to 0.003 - almost no physical nudging
const CURVE_NUDGE_MULTIPLIER = 1.0; // Reduced from 1.2 to 1.0 - no extra curve nudging, focus on steering
const SLIGHT_OUTWARD_ANGLE_ADJUST = 0.05; // Reduced from 0.1 to 0.05 for smoother wall sliding
const BOUNCE_RECOVERY_TURN_FACTOR = 0.12; // Increased from 0.08 to 0.12 for faster recovery from wall bounces
const BOUNCE_DURATION_MS = 400; // Reduced from 600 to 400 for shorter, more fluid bounce recovery
const BOUNCE_DURATION_FRAMES = Math.round(BOUNCE_DURATION_MS / GAME_TICK_RATE);
const CURVE_ESCAPE_THRESHOLD = 0.3; // Speed threshold below which curve escape is easier

// NEW: Track Center Magnetism - pulls cars back toward racing line when stuck in curves
const TRACK_CENTER_MAGNETISM = 0.008; // Reduced from 0.015 to 0.008 - gentler position pull
const CURVE_CENTER_ASSIST_THRESHOLD = 1.2; // Increased from 0.8 to 1.2 - activate at higher speeds
const CURVE_STEERING_ASSIST = 0.25; // Increased from 0.08 to 0.25 - much stronger steering assistance

app.get('/controller.html', (req, res) => res.sendFile(path.join(__dirname, 'controller.html')));
app.get('/', (req, res) => res.sendFile(path.join(__dirname, 'host.html')));
app.get('/host.html', (req, res) => res.sendFile(path.join(__dirname, 'host.html')));
app.use('/images', express.static(path.join(__dirname, 'images')));

function broadcast(message, excludeClientId = null) {
    clients.forEach((clientWs, id) => {
        if (id !== excludeClientId && clientWs.readyState === WebSocket.OPEN) {
            try { clientWs.send(JSON.stringify(message)); } catch (e) { console.error(`Error sending to client ${id}:`, e); }
        }
    });
}
function normalizeAngle(angle) {
    while (angle > Math.PI) angle -= 2 * Math.PI;
    while (angle < -Math.PI) angle += 2 * Math.PI;
    return angle;
}

function updatePlayerState(player) {
    if (!player || !player.controls) return;
    const previousPlayerX = player.x; const previousPlayerY = player.y;
    
    // Handle boost timing
    if (player.boostEndTime && Date.now() > player.boostEndTime) {
        player.boostEndTime = null;
        player.hasBoost = false;
    }
    
    // Check for boost pickups
    boosts.forEach((boost, boostId) => {
        const dx = player.x - boost.x;
        const dy = player.y - boost.y;
        const distance = Math.sqrt(dx * dx + dy * dy);
        
        if (distance < BOOST_PICKUP_RADIUS) {
            // Player picked up boost
            player.hasBoost = true;
            player.boostEndTime = Date.now() + BOOST_DURATION;
            boosts.delete(boostId);
            console.log(`Player ${player.id} (${player.name}) picked up boost!`);
        }
    });
    
    player.showHeadlights = (player.controls.left || player.controls.right) && player.speed > 0.5; 
    player.showReverseLights = player.controls.reverse && player.speed < -0.1; 

    if (player.isBouncing && player.bounceRecoveryFrames > 0) {
        const angleDiffToBounceDir = normalizeAngle(player.velocityAngle - player.angle);
        player.angle += angleDiffToBounceDir * BOUNCE_RECOVERY_TURN_FACTOR;
        player.bounceRecoveryFrames--;
        if (player.bounceRecoveryFrames <= 0) {
            player.isBouncing = false;
        }
    } else { 
        player.isBouncing = false; 
        let visualTurnRate = TURN_SPEED_FACTOR;
        if (Math.abs(player.speed) > 0.1) {
            let speedEffectOnTurn = (player.speed > 0) ? (player.speed / MAX_SPEED) : (Math.abs(player.speed) / Math.abs(MAX_REVERSE_SPEED)) * 0.7;
            speedEffectOnTurn = Math.max(0.3, Math.min(1.0, speedEffectOnTurn));
            let turnDirectionMultiplier = (player.speed >= 0) ? 1 : -1;
            if (player.controls.left) player.angle -= visualTurnRate * speedEffectOnTurn * turnDirectionMultiplier;
            if (player.controls.right) player.angle += visualTurnRate * speedEffectOnTurn * turnDirectionMultiplier;
        }
    }
    player.angle = normalizeAngle(player.angle);
    
    let intendedSpeed = player.speed; 
    if (!player.isBouncing) { 
        if (player.controls.throttle) intendedSpeed += ACCELERATION;
        else if (player.controls.reverse) intendedSpeed -= REVERSE_ACCELERATION;
        else { 
            if (intendedSpeed > 0) { intendedSpeed -= DECELERATION; if (intendedSpeed < 0) intendedSpeed = 0; } 
            else if (intendedSpeed < 0) { intendedSpeed += DECELERATION; if (intendedSpeed > 0) intendedSpeed = 0; } 
        }
        intendedSpeed = Math.max(MAX_REVERSE_SPEED, Math.min(intendedSpeed, MAX_SPEED)); 
        
        // FIXED: Apply boost - actually makes player faster, not just increases limit
        if (player.hasBoost) {
            const boostedMaxSpeed = MAX_SPEED * BOOST_SPEED_MULTIPLIER;
            // If player is going forward, boost their actual speed significantly
            if (intendedSpeed > 0) {
                intendedSpeed = Math.max(intendedSpeed, MAX_SPEED * 1.5); // Immediate speed boost
                intendedSpeed = Math.min(intendedSpeed, boostedMaxSpeed); // But cap at boost max
            }
            // Normal speed limit expansion for higher speeds
            intendedSpeed = Math.max(MAX_REVERSE_SPEED, Math.min(intendedSpeed, boostedMaxSpeed));
        }
    }
    
    if (!player.isBouncing) { 
        const angleDifference = normalizeAngle(player.angle - player.velocityAngle);
        let effectiveDriftFactor = DRIFT_FACTOR * (Math.abs(intendedSpeed) / MAX_SPEED);
        if (intendedSpeed < 0) effectiveDriftFactor *= 0.2; // Reduced from 0.5 to 0.2 - much less sensitive drift in reverse
        player.velocityAngle += angleDifference * effectiveDriftFactor; 
    }
    player.velocityAngle = normalizeAngle(player.velocityAngle);
    
    const currentSpeedForMovement = player.isBouncing ? player.speed : intendedSpeed; 
    const movementAngleForTrig = player.velocityAngle - (Math.PI / 2);
    let prospectiveX = player.x + Math.cos(movementAngleForTrig) * currentSpeedForMovement;
    let prospectiveY = player.y + Math.sin(movementAngleForTrig) * currentSpeedForMovement;
    
    let collided = false; 
    let collisionNormalX = 0; 
    let collisionNormalY = 0;
    let isInCurve = false; // Track if collision is in a curve

    if (prospectiveX >= COLLISION_PARAMS.straightMinX && prospectiveX <= COLLISION_PARAMS.straightMaxX) {
        if (prospectiveY < COLLISION_PARAMS.topStraightOuterY) { collided = true; collisionNormalY = 1; prospectiveY = COLLISION_PARAMS.topStraightOuterY; }
        else if (prospectiveY > COLLISION_PARAMS.topStraightInnerY && prospectiveY < COLLISION_PARAMS.curveCenterY) { collided = true; collisionNormalY = -1; prospectiveY = COLLISION_PARAMS.topStraightInnerY; }
        else if (prospectiveY > COLLISION_PARAMS.bottomStraightOuterY) { collided = true; collisionNormalY = -1; prospectiveY = COLLISION_PARAMS.bottomStraightOuterY; }
        else if (prospectiveY < COLLISION_PARAMS.bottomStraightInnerY && prospectiveY > COLLISION_PARAMS.curveCenterY) { collided = true; collisionNormalY = 1; prospectiveY = COLLISION_PARAMS.bottomStraightInnerY; }
    } else if (prospectiveX < COLLISION_PARAMS.straightMinX) {
        // Left curve collision detection - EXTREMELY TIGHT BOUNDARIES
        isInCurve = true;
        const dx = prospectiveX - COLLISION_PARAMS.leftCurveCenterX; 
        const dy = prospectiveY - COLLISION_PARAMS.curveCenterY; 
        const distSq = dx * dx + dy * dy;
        
        // Almost no overshoot allowed - stick very close to visual track
        const escapeMultiplier = (Math.abs(player.speed) < CURVE_ESCAPE_THRESHOLD) ? 1.02 : 1.01;
        const effectiveOuterRadius = COLLISION_PARAMS.curveOuterRadius * escapeMultiplier;
        
        if (distSq > effectiveOuterRadius ** 2) { 
            collided = true; 
            const dist = Math.sqrt(distSq); 
            if (dist > 0) { 
                collisionNormalX = -dx / dist; 
                collisionNormalY = -dy / dist; 
            } 
            // Place car exactly at track boundary - no visible overshoot
            const cushionFactor = 1.0; // Exactly at the boundary
            prospectiveX = COLLISION_PARAMS.leftCurveCenterX + dx/dist * COLLISION_PARAMS.curveOuterRadius * cushionFactor; 
            prospectiveY = COLLISION_PARAMS.curveCenterY + dy/dist * COLLISION_PARAMS.curveOuterRadius * cushionFactor;
        }
        else if (distSq < COLLISION_PARAMS.curveInnerRadius ** 2 && COLLISION_PARAMS.curveInnerRadius > 0) { 
            collided = true; 
            const dist = Math.sqrt(distSq); 
            if (dist > 0) { 
                collisionNormalX = dx / dist; 
                collisionNormalY = dy / dist; 
            } 
            prospectiveX = COLLISION_PARAMS.leftCurveCenterX + dx/dist * COLLISION_PARAMS.curveInnerRadius; 
            prospectiveY = COLLISION_PARAMS.curveCenterY + dy/dist * COLLISION_PARAMS.curveInnerRadius;
        }
    } else if (prospectiveX > COLLISION_PARAMS.straightMaxX) {
        // Right curve collision detection - EXTREMELY TIGHT BOUNDARIES
        isInCurve = true;
        const dx = prospectiveX - COLLISION_PARAMS.rightCurveCenterX; 
        const dy = prospectiveY - COLLISION_PARAMS.curveCenterY; 
        const distSq = dx * dx + dy * dy;
        
        // Almost no overshoot allowed - stick very close to visual track
        const escapeMultiplier = (Math.abs(player.speed) < CURVE_ESCAPE_THRESHOLD) ? 1.02 : 1.01;
        const effectiveOuterRadius = COLLISION_PARAMS.curveOuterRadius * escapeMultiplier;
        
        if (distSq > effectiveOuterRadius ** 2) { 
            collided = true; 
            const dist = Math.sqrt(distSq); 
            if (dist > 0) { 
                collisionNormalX = -dx / dist; 
                collisionNormalY = -dy / dist; 
            } 
            // Place car exactly at track boundary - no visible overshoot
            const cushionFactor = 1.0; // Exactly at the boundary
            prospectiveX = COLLISION_PARAMS.rightCurveCenterX + dx/dist * COLLISION_PARAMS.curveOuterRadius * cushionFactor; 
            prospectiveY = COLLISION_PARAMS.curveCenterY + dy/dist * COLLISION_PARAMS.curveOuterRadius * cushionFactor;
        }
        else if (distSq < COLLISION_PARAMS.curveInnerRadius ** 2 && COLLISION_PARAMS.curveInnerRadius > 0) { 
            collided = true; 
            const dist = Math.sqrt(distSq); 
            if (dist > 0) { 
                collisionNormalX = dx / dist; 
                collisionNormalY = dy / dist; 
            } 
            prospectiveX = COLLISION_PARAMS.rightCurveCenterX + dx/dist * COLLISION_PARAMS.curveInnerRadius; 
            prospectiveY = COLLISION_PARAMS.curveCenterY + dy/dist * COLLISION_PARAMS.curveInnerRadius;
        }
    }

    if (collided) {
        player.x = prospectiveX; 
        player.y = prospectiveY;
        player.speed = intendedSpeed * WALL_SLIDE_SPEED_REDUCTION; 
        if ((player.controls.throttle && player.speed >= 0) || (player.controls.reverse && player.speed <= 0)) {
            if (Math.abs(player.speed) < MIN_SLIDE_SPEED) {
                player.speed = Math.sign(player.speed || (player.controls.throttle ? 1 : -1)) * MIN_SLIDE_SPEED;
            }
        } else if (Math.abs(player.speed) < 0.1) {
            player.speed = 0;
        }
        
        // Add slight velocity damping to prevent oscillation
        const dampingFactor = isInCurve ? 0.88 : 0.94; // Increased damping in curves to prevent bouncing
        player.speed *= dampingFactor;
        
        // DISABLE bouncing and steering assistance when going in reverse to prevent weird physics
        const isGoingReverse = player.speed < 0;
        
        if (!isGoingReverse) {
            // Normal forward collision handling with bouncing
            const tangentX = -collisionNormalY;
            const tangentY = collisionNormalX;
            const currentMovementAngleRad = player.velocityAngle - Math.PI / 2;
            const currentDirX = Math.cos(currentMovementAngleRad);
            const currentDirY = Math.sin(currentMovementAngleRad);
            const dotProductWithTangent = currentDirX * tangentX + currentDirY * tangentY;
            let slideDirX = tangentX * Math.sign(dotProductWithTangent >= 0 ? 1 : -1); 
            let slideDirY = tangentY * Math.sign(dotProductWithTangent >= 0 ? 1 : -1);
            
            // More emphasis on steering assistance in curves rather than physical bouncing
            if (isInCurve) {
                // Very gentle steering assist toward track center for curves - minimal intervention
                let targetCenterX, targetCenterY;
                if (player.x < COLLISION_PARAMS.straightMinX) {
                    // Left curve center direction
                    const angle = Math.atan2(player.y - COLLISION_PARAMS.curveCenterY, player.x - COLLISION_PARAMS.leftCurveCenterX);
                    targetCenterX = COLLISION_PARAMS.leftCurveCenterX + Math.cos(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
                    targetCenterY = COLLISION_PARAMS.curveCenterY + Math.sin(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
                } else {
                    // Right curve center direction
                    const angle = Math.atan2(player.y - COLLISION_PARAMS.curveCenterY, player.x - COLLISION_PARAMS.rightCurveCenterX);
                    targetCenterX = COLLISION_PARAMS.rightCurveCenterX + Math.cos(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
                    targetCenterY = COLLISION_PARAMS.curveCenterY + Math.sin(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
                }
                
                const centerDirX = targetCenterX - player.x;
                const centerDirY = targetCenterY - player.y;
                const centerDirMag = Math.sqrt(centerDirX * centerDirX + centerDirY * centerDirY);
                
                if (centerDirMag > 0.01) {
                    const normalizedCenterDirX = centerDirX / centerDirMag;
                    const normalizedCenterDirY = centerDirY / centerDirMag;
                    
                    // Minimal steering toward center - barely noticeable intervention
                    const centerBlend = 0.15; // Reduced from 0.35 to 0.15 - very subtle
                    slideDirX = (slideDirX * (1 - centerBlend)) + (normalizedCenterDirX * centerBlend);
                    slideDirY = (slideDirY * (1 - centerBlend)) + (normalizedCenterDirY * centerBlend);
                    
                    // Very subtle steering correction - barely perceptible
                    const centerAngle = Math.atan2(centerDirY, centerDirX) + Math.PI / 2;
                    const angleDiff = normalizeAngle(centerAngle - player.angle);
                    player.angle += angleDiff * 0.02; // Reduced from 0.04 to 0.02 - extremely gentle
                    player.angle = normalizeAngle(player.angle);
                }
            } else {
                // Normal handling for straight sections
                const curveEscapeAdjust = SLIGHT_OUTWARD_ANGLE_ADJUST;
                slideDirX = (slideDirX * (1 - curveEscapeAdjust)) + (collisionNormalX * curveEscapeAdjust);
                slideDirY = (slideDirY * (1 - curveEscapeAdjust)) + (collisionNormalY * curveEscapeAdjust);
            }
            
            const slideMag = Math.sqrt(slideDirX * slideDirX + slideDirY * slideDirY);
            if (slideMag > 0.01) {
                slideDirX /= slideMag;
                slideDirY /= slideMag;
            }
            const newMovementAngle = Math.atan2(slideDirY, slideDirX);
            player.velocityAngle = normalizeAngle(newMovementAngle + Math.PI / 2); 
            player.isBouncing = true; 
            player.bounceRecoveryFrames = BOUNCE_DURATION_FRAMES; 
            
            // Gentler physical nudging - more natural feel
            const nudgeForce = isInCurve ? WALL_NUDGE_AWAY_FORCE * CURVE_NUDGE_MULTIPLIER : WALL_NUDGE_AWAY_FORCE;
            player.x += collisionNormalX * nudgeForce; 
            player.y += collisionNormalY * nudgeForce;
        } else {
            // REVERSE MODE: Simple collision handling without bouncing or steering assistance
            // Just stop the car gently at the wall without complex physics
            player.isBouncing = false;
            player.bounceRecoveryFrames = 0;
            
            // Extra damping for reverse to prevent oscillation and swaying
            const reverseDampingFactor = isInCurve ? 0.75 : 0.85; // More aggressive damping in curves
            player.speed *= reverseDampingFactor;
            
            // Simple wall slide for reverse - just follow the wall tangent
            const tangentX = -collisionNormalY;
            const tangentY = collisionNormalX;
            const currentMovementAngleRad = player.velocityAngle - Math.PI / 2;
            const currentDirX = Math.cos(currentMovementAngleRad);
            const currentDirY = Math.sin(currentMovementAngleRad);
            const dotProductWithTangent = currentDirX * tangentX + currentDirY * tangentY;
            let slideDirX = tangentX * Math.sign(dotProductWithTangent >= 0 ? 1 : -1); 
            let slideDirY = tangentY * Math.sign(dotProductWithTangent >= 0 ? 1 : -1);
            
            // Smooth out the sliding direction for more stable reverse handling
            const smoothingFactor = 0.7; // Blend with previous velocity direction for stability
            const prevVelX = Math.cos(currentMovementAngleRad);
            const prevVelY = Math.sin(currentMovementAngleRad);
            slideDirX = (slideDirX * (1 - smoothingFactor)) + (prevVelX * smoothingFactor);
            slideDirY = (slideDirY * (1 - smoothingFactor)) + (prevVelY * smoothingFactor);
            
            const newMovementAngle = Math.atan2(slideDirY, slideDirX);
            player.velocityAngle = normalizeAngle(newMovementAngle + Math.PI / 2);
            
            // Much more minimal nudging for reverse - just enough to unstick
            const gentleNudgeForce = WALL_NUDGE_AWAY_FORCE * 0.1; // Reduced from 0.3 to 0.1 - extremely gentle
            player.x += collisionNormalX * gentleNudgeForce; 
            player.y += collisionNormalY * gentleNudgeForce;
        }
    } else { 
        player.x = prospectiveX; 
        player.y = prospectiveY; 
        player.speed = intendedSpeed; 
        if (player.bounceRecoveryFrames <= 0) {
            player.isBouncing = false;
        }
    }
    
    // NEW: Track Center Magnetism - gradual pull toward racing line in curves
    if (isInCurve && Math.abs(player.speed) < CURVE_CENTER_ASSIST_THRESHOLD) {
        // DISABLE magnetism when going in reverse to prevent interference
        const isGoingReverse = player.speed < 0;
        
        if (!isGoingReverse) {
            let targetX, targetY;
            
            // Determine track center based on which curve we're in
            if (player.x < COLLISION_PARAMS.straightMinX) {
                // Left curve - target the centerline of the curve
                const angle = Math.atan2(player.y - COLLISION_PARAMS.curveCenterY, player.x - COLLISION_PARAMS.leftCurveCenterX);
                targetX = COLLISION_PARAMS.leftCurveCenterX + Math.cos(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
                targetY = COLLISION_PARAMS.curveCenterY + Math.sin(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
            } else {
                // Right curve - target the centerline of the curve  
                const angle = Math.atan2(player.y - COLLISION_PARAMS.curveCenterY, player.x - COLLISION_PARAMS.rightCurveCenterX);
                targetX = COLLISION_PARAMS.rightCurveCenterX + Math.cos(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
                targetY = COLLISION_PARAMS.curveCenterY + Math.sin(angle) * TRACK_CURVE_RADIUS_CENTERLINE;
            }
            
            // Apply gentle magnetism toward track center
            const centerDx = targetX - player.x;
            const centerDy = targetY - player.y;
            const centerDistance = Math.sqrt(centerDx * centerDx + centerDy * centerDy);
            
            if (centerDistance > 5) { // Only apply if not already at center
                const magnetismX = (centerDx / centerDistance) * TRACK_CENTER_MAGNETISM;
                const magnetismY = (centerDy / centerDistance) * TRACK_CENTER_MAGNETISM;
                
                player.x += magnetismX;
                player.y += magnetismY;
                
                // Also gently adjust velocity angle toward center if moving very slowly
                if (Math.abs(player.speed) < 0.2) {
                    const centerAngle = Math.atan2(centerDy, centerDx) + Math.PI / 2;
                    const angleDiff = normalizeAngle(centerAngle - player.velocityAngle);
                    player.velocityAngle += angleDiff * CURVE_STEERING_ASSIST;
                    player.velocityAngle = normalizeAngle(player.velocityAngle);
                }
            }
        }
    }
    
    const crossedFinishLineThisFrame = (previousPlayerX < FINISH_LINE_X && player.x >= FINISH_LINE_X);
    const withinFinishLineY = (player.y >= FINISH_LINE_Y_START_EDGE && player.y <= FINISH_LINE_Y_END_EDGE);
    const xVelocity = player.x - previousPlayerX;
    const correctDirection = (LAP_DIRECTION_X > 0 && xVelocity > 0.05); 
    if (crossedFinishLineThisFrame && withinFinishLineY && correctDirection) {
        if (!player.onLap) { player.onLap = true; player.lapStartTime = Date.now(); player.justCompletedLap = false; console.log(`Player ${player.id} (${player.name}) STARTED lap ${player.lapCount + 1}`); }
        else if (player.onLap && !player.justCompletedLap) { const currentTime = Date.now(); const lapDuration = currentTime - player.lapStartTime; if (lapDuration > 1000) { player.lapCount++; player.lastLapTime = lapDuration; if (player.bestLapTime === 0 || lapDuration < player.bestLapTime) player.bestLapTime = lapDuration; console.log(`P ${player.id} (${player.name}) COMPLETED lap ${player.lapCount}. T: ${lapDuration/1000}s. B: ${player.bestLapTime/1000}s`); player.lapStartTime = currentTime; player.justCompletedLap = true; } }
    } else { if (player.justCompletedLap && (player.x < FINISH_LINE_X - 20 || player.x > FINISH_LINE_X + 20) ) player.justCompletedLap = false; }
}

function spawnBoost() {
    // Only spawn boosts if there are active players
    if (players.size === 0) {
        return;
    }
    
    // Don't spawn if we already have boosts at both locations
    if (boosts.size >= BOOST_LOCATIONS.length) {
        return;
    }
    
    // Find available locations (not already occupied)
    const availableLocations = BOOST_LOCATIONS.filter(location => {
        return !Array.from(boosts.values()).some(existingBoost => {
            const dx = existingBoost.x - location.x;
            const dy = existingBoost.y - location.y;
            const distance = Math.sqrt(dx * dx + dy * dy);
            return distance < 50; // Don't spawn within 50px of existing boost
        });
    });
    
    if (availableLocations.length === 0) {
        return; // No available locations
    }
    
    const location = availableLocations[Math.floor(Math.random() * availableLocations.length)];
    const boostId = nextBoostId++;
    boosts.set(boostId, {
        id: boostId,
        x: location.x,
        y: location.y,
        spawnTime: Date.now()
    });
    console.log(`Boost spawned at ${location.location}`);
}

function gameTick() {
    if (players.size === 0) return;
    players.forEach(player => { updatePlayerState(player); });
    const gameState = { 
        type: 'gameStateUpdate', 
        players: Array.from(players.values()),
        boosts: Array.from(boosts.values())
    };
    if (ARTIFICIAL_OUTPUT_DELAY_MS > 0) {
        setTimeout(() => { broadcast(gameState); }, ARTIFICIAL_OUTPUT_DELAY_MS);
    } else {
        broadcast(gameState);
    }
}

wss.on('connection', (ws, req) => {
    const clientId = clientIdCounter++; clients.set(clientId, ws);
    console.log(`Client ${clientId} connected from IP: ${req.socket.remoteAddress}`);
    try { ws.send(JSON.stringify({ type: 'welcome', clientId: clientId, message: 'Welcome! Announce if host.' })); } catch (e) {}
    const existingPlayersData = Array.from(players.values());
    if (existingPlayersData.length > 0) { try { ws.send(JSON.stringify({ type: 'existingPlayers', players: existingPlayersData })); } catch (e) {} }

    ws.on('message', (incomingMessage) => { 
        let parsedMessage; const messageString = incomingMessage.toString();
        try { parsedMessage = JSON.parse(messageString); } 
        catch (error) { 
            console.error(`Invalid JSON from client ${clientId}: '${messageString}'`, error); 
            try { ws.send(JSON.stringify({ type: 'error', message: 'Invalid JSON format.' })); } catch(e) {/*ignore*/}
            return; 
        }
        
        const playerNameForLog = players.get(clientId)?.name || 'SetupInProgress';
        if (parsedMessage.type !== 'controlInput') {
             console.log(`Msg from client ${clientId} (${playerNameForLog}): Type: ${parsedMessage.type}`);
        }

        if (parsedMessage.type === 'hostAnnounce') {
            console.log(`Client ${clientId} announced as host.`);
            const networkInterfaces = os.networkInterfaces();
            let serverIPs = [];
            
            // Get all IPv4 addresses
            for (const name of Object.keys(networkInterfaces)) {
                for (const net of networkInterfaces[name]) {
                    if (net.family === 'IPv4' && !net.internal) {
                        serverIPs.push(net.address);
                    }
                }
            }
            
            // If no external IPs found (cloud hosting scenario), use the request IP or localhost
            if (serverIPs.length === 0) {
                const requestIP = req.headers['x-forwarded-for'] || req.socket.remoteAddress || 'localhost';
                if (requestIP !== '::1' && requestIP !== '127.0.0.1') {
                    serverIPs.push(requestIP.replace('::ffff:', '')); // Clean IPv6 wrapper
                } else {
                    serverIPs.push('localhost');
                }
            }
            
            console.log("Server IPs for QR Code (sending to host):", serverIPs);
            try {
                ws.send(JSON.stringify({ type: 'serverInfo', ipAddresses: serverIPs, port: PORT }));
            } catch (e) { console.error(`Error sending serverInfo to host ${clientId}:`, e); }
        } else if (parsedMessage.type === 'playerSetup') {
            // Check if game is full (8 players max)
            if (players.size >= 8) {
                try {
                    ws.send(JSON.stringify({ type: 'error', message: 'Game is full! Maximum 8 players allowed.' }));
                } catch (e) { console.error(`Error sending game full message to ${clientId}:`, e); }
                console.log(`Player ${clientId} rejected - game is full (${players.size}/8 players)`);
                return;
            }
            
            const startPosConfig = startingPositions[nextStartPositionIndex % startingPositions.length];
            nextStartPositionIndex++;
            const playerData = {
                id: clientId, name: parsedMessage.name || `Player${clientId}`,
                carId: parsedMessage.carId || 'Race_car_01',
                x: FINISH_LINE_X + startPosConfig.x_offset, 
                y: TRACK_BOTTOM_STRAIGHT_Y + startPosConfig.y_offset,
                angle: startPosConfig.angle,
                velocityAngle: startPosConfig.angle, speed: 0, width: 18, height: 32,
                controls: { left: false, right: false, throttle: false, reverse: false },
                lapCount: 0, lapStartTime: 0, lastLapTime: 0, bestLapTime: 0,
                onLap: false, justCompletedLap: false,
                previousXPosition: FINISH_LINE_X + startPosConfig.x_offset,
                previousYPosition: TRACK_BOTTOM_STRAIGHT_Y + startPosConfig.y_offset,
                showHeadlights: false,
                showReverseLights: false,
                isBouncing: false, 
                bounceRecoveryFrames: 0,
                hasBoost: false,
                boostEndTime: null
            };
            players.set(clientId, playerData);
            console.log(`Player ${clientId} (${playerData.name}) setup with car: ${playerData.carId}.`);
            broadcast({ type: 'newPlayer', player: playerData }); 
        } else if (parsedMessage.type === 'controlInput') {
            const playerToUpdate = players.get(clientId);
            if (playerToUpdate && parsedMessage.controls) {
                if (ARTIFICIAL_INPUT_DELAY_MS > 0) {
                    setTimeout(() => {
                        const currentPlayer = players.get(clientId); 
                        if (currentPlayer) { currentPlayer.controls = parsedMessage.controls; }
                    }, ARTIFICIAL_INPUT_DELAY_MS);
                } else {
                    playerToUpdate.controls = parsedMessage.controls;
                }
            }
        } else { 
            console.log(`Unknown msg type from ${clientId}: ${parsedMessage.type}`);
        }
    });
    ws.on('close', () => {
        clients.delete(clientId); const removedPlayer = players.get(clientId);
        if (removedPlayer) { players.delete(clientId); console.log(`Client ${clientId} (${removedPlayer.name}) disconnected.`); broadcast({ type: 'playerLeft', clientId: clientId });
        } else { console.log(`Client ${clientId} (not player) disconnected.`); }
    });
    ws.on('error', (error) => {
        console.error(`Error with client ${clientId}:`, error);
        if (ws.readyState !== WebSocket.OPEN && ws.readyState !== WebSocket.CONNECTING) {
            clients.delete(clientId); const removedPlayerOnError = players.get(clientId);
            if (removedPlayerOnError) { players.delete(clientId); console.log(`Client ${clientId} (${removedPlayerOnError.name}) removed on error.`); broadcast({ type: 'playerLeft', clientId: clientId });
            } else { console.log(`Client ${clientId} (not player) removed on error.`); }
        }
    });
});

server.listen(PORT, () => {
    console.log(`HTTP and WebSocket server started on port ${PORT}`);
    console.log(`Game tick rate: ${GAME_TICK_RATE}ms (~${Math.round(1000/GAME_TICK_RATE)} Hz)`);
    if (ARTIFICIAL_INPUT_DELAY_MS > 0 || ARTIFICIAL_OUTPUT_DELAY_MS > 0) {
        console.warn(`ARTIFICIAL LATENCY ENABLED: Input delay=${ARTIFICIAL_INPUT_DELAY_MS}ms, Output delay=${ARTIFICIAL_OUTPUT_DELAY_MS}ms`);
    }
    const networkInterfaces = os.networkInterfaces();
    console.log("Server is listening on these IPv4 addresses:");
    Object.keys(networkInterfaces).forEach((ifaceName) => {
        networkInterfaces[ifaceName].forEach((iface) => {
            if (iface.family === 'IPv4' && !iface.internal) {
                console.log(`  ${ifaceName}: http://${iface.address}:${PORT}`);
            }
        });
    });
    console.log(`  Controller URL (example): http://<YOUR_LOCAL_IP_FROM_ABOVE>:${PORT}/controller.html`);
    console.log('Waiting for connections...');
    setInterval(gameTick, GAME_TICK_RATE); 
    setInterval(spawnBoost, BOOST_SPAWN_INTERVAL); // Spawn boosts every 15 seconds
});