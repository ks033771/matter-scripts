/* ==========================================================
   Matter.js + Canvas-Renderer (optimiert)
   - Kein Matter.Render, eigener RAF-Loop (semi-fixed timestep)
   - DPR capped, Dirty-Rect-Heuristik, adaptive Frame-Skips
   - Scroll+Wheel gebündelt, sanft geglättet
   - SVG-Parsing in kleinen Häppchen (Chrome-freundlicher)
   ========================================================== */

/* ---------- Konfiguration ---------- */
const THICCNESS = 120;
const TOP_WALL_OFFSET = 400;
const SVG_PATH_SELECTOR = "#matter-path";
const SVG_WIDTH_IN_PX = 500;
const SVG_WIDTH_AS_PERCENT_OF_CONTAINER_WIDTH = 0.30;

const PHYSICS = {
  GRAVITY_X: 0,
  GRAVITY_Y: 1.0,
  GRAVITY_SCALE: 0.00125,
  ENABLE_SLEEPING: true,
  POSITION_ITERATIONS: 4,
  VELOCITY_ITERATIONS: 4,
  CONSTRAINT_ITERATIONS: 1
};

const BODY_DEFAULTS = {
  restitution: 0.35,
  friction: 0.3,
  frictionStatic: 0.5,
  frictionAir: 0.0012,
  density: 0.001
};

const SVG_OPTS = { sample: 6, simplifyTolerance: 10.2 };

const LAYOUT = {
  marginPct: 0.07,
  startYRatio: 0.12,
  kickLinear: 0.35,
  kickAngular: 0.02
};

const RESPONSIVE_SIZE = [
  { maxViewportWidth: 480,   percentOfContainer: 0.6, minPx: 150 },
  { maxViewportWidth: 768,   percentOfContainer: 0.6, minPx: 175 },
  { maxViewportWidth: Infinity, percentOfContainer: SVG_WIDTH_AS_PERCENT_OF_CONTAINER_WIDTH, minPx: 0 }
];

const SCROLL_TRIGGER = {
  energyPerPx: (function () {
    const isDesktop = window.matchMedia("(pointer: fine)").matches;
    return isDesktop ? 0.5 : 0.5;
  })(),
  baseAccelPerEnergy: 0.000015,
  capAccelPerSec: 0.0000056,
  tauMs: 360,
  viewportGuard: true,
  upOnly: true,
  angularJitter: 0.01,
  easePerSec: 0.06,
  antiSagBias: 0.05
};

const RENDER = {
  DPR_CAP: 1.35,
  TARGET_FPS: 60,
  MOVE_EPS_POS: 0.2,
  MOVE_EPS_ANG: 0.002
};

/* ---------- DOM ---------- */
const matterContainer = document.querySelector("#matter-container");
if (!matterContainer) {
  console.warn("[matter-canvas] #matter-container fehlt.");
}

/* ---------- Matter Aliases ---------- */
const { Engine, Runner, Bodies, Composite, Body, Svg, Vector, Vertices, Common, Events } = Matter;
if (window.decomp) Common.setDecomp(window.decomp);

/* ---------- Engine ---------- */
const engine = Engine.create();
engine.enableSleeping = PHYSICS.ENABLE_SLEEPING;
engine.world.gravity.x = PHYSICS.GRAVITY_X;
engine.world.gravity.y = PHYSICS.GRAVITY_Y;
engine.world.gravity.scale = PHYSICS.GRAVITY_SCALE;
engine.positionIterations = PHYSICS.POSITION_ITERATIONS;
engine.velocityIterations = PHYSICS.VELOCITY_ITERATIONS;
engine.constraintIterations = PHYSICS.CONSTRAINT_ITERATIONS;

const FIXED_DT = 1000 / 60;
let accumulatorMs = 0;

/* ---------- EIN Canvas für alle Sprites ---------- */
const spriteCanvas = document.createElement("canvas");
const ctx = spriteCanvas.getContext("2d", { alpha: true, desynchronized: true });
spriteCanvas.style.position = "absolute";
spriteCanvas.style.left = "0";
spriteCanvas.style.top = "0";
spriteCanvas.style.pointerEvents = "none";
matterContainer.style.position = "relative";
matterContainer.appendChild(spriteCanvas);

function dpr() {
  return Math.min(RENDER.DPR_CAP, window.devicePixelRatio || 1);
}

function resizeSpriteCanvas() {
  const pr = dpr();
  const w = matterContainer.clientWidth | 0;
  const h = matterContainer.clientHeight | 0;
  spriteCanvas.width = Math.max(1, Math.floor(w * pr));
  spriteCanvas.height = Math.max(1, Math.floor(h * pr));
  spriteCanvas.style.width = w + "px";
  spriteCanvas.style.height = h + "px";
  ctx.setTransform(pr, 0, 0, pr, 0, 0);
}
resizeSpriteCanvas();

/* ---------- Utilities ---------- */
function getResponsiveRule() {
  const vw = window.innerWidth || document.documentElement.clientWidth || 1024;
  return RESPONSIVE_SIZE.find(r => vw <= r.maxViewportWidth) || RESPONSIVE_SIZE[RESPONSIVE_SIZE.length - 1];
}

function getTargetWidth() {
  const rule = getResponsiveRule();
  const base = matterContainer.clientWidth;
  const raw = base * rule.percentOfContainer;
  return Math.max(rule.minPx || 0, raw);
}

function currentScale() {
  return getTargetWidth() / SVG_WIDTH_IN_PX;
}

function ensureClosed(verts) {
  if (!verts.length) return verts;
  const a = verts[0], b = verts[verts.length - 1];
  const dx = a.x - b.x, dy = a.y - b.y;
  if (dx * dx + dy * dy > 1e-6) verts = verts.concat([{ x: a.x, y: a.y }]);
  return verts;
}

function polygonArea(verts) {
  let area = 0;
  for (let i = 0, j = verts.length - 1; i < verts.length; j = i++) {
    area += verts[j].x * verts[i].y - verts[i].x * verts[j].y;
  }
  return 0.5 * area;
}

// DP Fallback
function simplifyDP(points, tol) {
  if (!tol || points.length <= 2) return points;
  const sqTol = tol * tol;

  function sqSegDist(p, a, b) {
    let x = a.x, y = a.y, dx = b.x - x, dy = b.y - y;
    if (dx !== 0 || dy !== 0) {
      const t = ((p.x - x) * dx + (p.y - y) * dy) / (dx * dx + dy * dy);
      if (t > 1) { x = b.x; y = b.y; }
      else if (t > 0) { x += dx * t; y += dy * t; }
    }
    dx = p.x - x; dy = p.y - y;
    return dx * dx + dy * dy;
  }

  function simplifyRadial(pts, sq) {
    let prev = pts[0], out = [prev], point;
    for (let i = 1; i < pts.length; i++) {
      point = pts[i];
      if ((point.x - prev.x) ** 2 + (point.y - prev.y) ** 2 > sq) {
        out.push(point);
        prev = point;
      }
    }
    if (prev !== point) out.push(point);
    return out;
  }

  function step(pts, first, last, sq, out) {
    let max = sq, idx;
    for (let i = first + 1; i < last; i++) {
      const d = sqSegDist(pts[i], pts[first], pts[last]);
      if (d > max) { idx = i; max = d; }
    }
    if (max > sq) {
      if (idx - first > 1) step(pts, first, idx, sq, out);
      out.push(pts[idx]);
      if (last - idx > 1) step(pts, idx, last, sq, out);
    }
  }

  const pts = simplifyRadial(points, sqTol);
  const last = pts.length - 1;
  const out = [pts[0]];
  step(pts, 0, last, sqTol, out);
  out.push(pts[last]);
  return out;
}

/* ---------- CSS-Variablen -> echte Farben ---------- */
function resolvePaint(pathEl) {
  const cs = getComputedStyle(pathEl);
  let fill = cs.fill && cs.fill !== "none" ? cs.fill : pathEl.getAttribute("fill");
  let stroke = cs.stroke && cs.stroke !== "none" ? cs.stroke : pathEl.getAttribute("stroke");
  if (!fill || /^var\(/.test(fill)) fill = "#222";
  if (!stroke || /^var\(/.test(stroke)) stroke = "";
  const strokeWidth = parseFloat(cs.strokeWidth || pathEl.getAttribute("stroke-width") || "0") || 0;
  return { fill, stroke, strokeWidth };
}

/* ---------- SVG -> Body + Path2D (inkrementell) ---------- */
const sourcePaths = Array.from(document.querySelectorAll(SVG_PATH_SELECTOR));
sourcePaths.forEach(p => { p.style.display = "none"; });

// globale Instanz-Arrays, werden später gefüllt
let instances = [];
let dynamicBodies = [];

function buildInstanceFromPath(pathEl, sharedTemp) {
  const d = pathEl.getAttribute("d") || "";
  const { fill, stroke, strokeWidth } = resolvePaint(pathEl);

  // Optimierung: ein temporäres <svg><path> wiederverwenden
  const tempSVG = sharedTemp.svg;
  const tempPath = sharedTemp.path;

  const chunks = d.split(/(?<=z|Z)\s*(?=M|m)/);
  let bestVerts = null, bestArea = -Infinity, bestCentroid = { x: 0, y: 0 };

  for (const seg of chunks) {
    const s = seg.trim();
    if (!s) continue;
    tempPath.setAttribute("d", s);

    let v = Svg.pathToVertices(tempPath, SVG_OPTS.sample);
    if (SVG_OPTS.simplifyTolerance && v.length > 8) { // leicht angehoben, um unnötige Arbeit zu sparen
      v = (typeof Vertices.simplify === "function")
        ? Vertices.simplify(v, SVG_OPTS.simplifyTolerance)
        : simplifyDP(v, SVG_OPTS.simplifyTolerance);
    }
    v = ensureClosed(v);
    const area = Math.abs(polygonArea(v));
    if (area > bestArea) {
      bestArea = area;
      bestVerts = v;
      bestCentroid = Vertices.centre(v);
    }
  }

  const scaleFactor = currentScale();
  const scaledVerts = Vertices.scale(bestVerts, scaleFactor, scaleFactor);
  const startX = matterContainer.clientWidth * 0.5;
  const startY = 0;
  const body = Bodies.fromVertices(startX, startY, [scaledVerts], { ...BODY_DEFAULTS, render: { visible: false } }, true);

  return {
    body,
    path2d: new Path2D(pathEl.getAttribute("d") || ""),
    style: { fill, stroke, lineWidth: strokeWidth },
    rawCentroid: bestCentroid
  };
}

/**
 * Inkrementelles Bauen aller Instanzen, damit Chrome nicht 2s am Stück blockt.
 */
function buildInstancesAsync(done) {
  if (!sourcePaths.length) {
    instances = [];
    dynamicBodies = [];
    done();
    return;
  }

  const sharedTempSVG = document.createElementNS("http://www.w3.org/2000/svg", "svg");
  const sharedTempPath = document.createElementNS("http://www.w3.org/2000/svg", "path");
  sharedTempSVG.appendChild(sharedTempPath);

  const sharedTemp = { svg: sharedTempSVG, path: sharedTempPath };

  instances = [];
  dynamicBodies = [];

  let index = 0;

  function step() {
    const start = performance.now();

    // mehrere Pfade pro Slice verarbeiten, aber nicht zu lange
    while (index < sourcePaths.length && performance.now() - start < 12) {
      const pathEl = sourcePaths[index++];
      const inst = buildInstanceFromPath(pathEl, sharedTemp);
      instances.push(inst);
      dynamicBodies.push(inst.body);
    }

    if (index < sourcePaths.length) {
      if ("requestIdleCallback" in window) {
        requestIdleCallback(step);
      } else {
        setTimeout(step, 0);
      }
    } else {
      done();
    }
  }

  // Start
  if ("requestIdleCallback" in window) {
    requestIdleCallback(step);
  } else {
    setTimeout(step, 0);
  }
}

/* ---------- Weltgrenzen ---------- */
let ground = Bodies.rectangle(
  matterContainer.clientWidth / 2,
  matterContainer.clientHeight + THICCNESS / 2,
  27184,
  THICCNESS,
  { isStatic: true }
);

let leftWall = Bodies.rectangle(
  -THICCNESS / 2,
  matterContainer.clientHeight / 2,
  THICCNESS,
  matterContainer.clientHeight * 5,
  { isStatic: true }
);

let rightWall = Bodies.rectangle(
  matterContainer.clientWidth + THICCNESS / 2,
  matterContainer.clientHeight / 2,
  THICCNESS,
  matterContainer.clientHeight * 5,
  { isStatic: true }
);

let ceiling = Bodies.rectangle(
  matterContainer.clientWidth / 2,
  -TOP_WALL_OFFSET - THICCNESS / 2,
  Math.max(27184, matterContainer.clientWidth * 3),
  THICCNESS,
  { isStatic: true }
);

/* ---------- Startlayout ---------- */
function layoutInstancesEvenly(list) {
  const W = matterContainer.clientWidth,
        H = matterContainer.clientHeight,
        n = list.length;
  if (!n) return;
  const margin = Math.max(24, W * LAYOUT.marginPct);
  for (let i = 0; i < n; i++) {
    const x = margin + ((W - 2 * margin) * (i + 0.5)) / n;
    const y = -40 - (Math.random() * 40);
    Body.setPosition(list[i].body, { x, y });
    Body.setVelocity(list[i].body, { x: (Math.random() - 0.5) * LAYOUT.kickLinear, y: 0 });
    Body.setAngularVelocity(list[i].body, (Math.random() - 0.5) * LAYOUT.kickAngular);
  }
}

/* ---------- Scroll/Wheel → sanfter Lift ---------- */
let isInView = false;
let lastScrollY = window.scrollY || window.pageYOffset || 0;
let emaDY = 0;
let liftEnergy = 0;
const HARD_SCROLL_CLAMP = 140;
const EMA_ALPHA = 0.75;

let lastScrollTimestamp = 0;
let activeScrollBurst = false;
const SCROLL_BURST_TIMEOUT = 50;

function handleLiftInput(dy) {
  dy = Math.max(-HARD_SCROLL_CLAMP, Math.min(HARD_SCROLL_CLAMP, dy));
  emaDY = EMA_ALPHA * emaDY + (1 - EMA_ALPHA) * dy;
  const add = Math.max(0, emaDY) * SCROLL_TRIGGER.energyPerPx;
  if (add > 0) {
    liftEnergy += add;
    lastScrollTimestamp = performance.now();
    activeScrollBurst = true;
  }
}

window.addEventListener("wheel", (ev) => {
  if (SCROLL_TRIGGER.viewportGuard && !isInView) return;
  if (SCROLL_TRIGGER.upOnly && ev.deltaY <= 0) return;
  handleLiftInput(ev.deltaY || 0);
}, { passive: true });

window.addEventListener("scroll", () => {
  const y = window.scrollY || window.pageYOffset || 0;
  const dy = y - lastScrollY;
  lastScrollY = y;
  if (SCROLL_TRIGGER.viewportGuard && !isInView) return;
  if (SCROLL_TRIGGER.upOnly && dy <= 0) return;
  handleLiftInput(dy);
}, { passive: true });

/* ---------- Draw ---------- */
let spriteScale = currentScale();
let prevSpriteScale = spriteScale;
let lastPositions = new WeakMap();

function drawSprites() {
  ctx.clearRect(0, 0, matterContainer.clientWidth, matterContainer.clientHeight);
  for (const inst of instances) {
    const { body, path2d, style, rawCentroid } = inst;
    const cx = rawCentroid.x * spriteScale;
    const cy = rawCentroid.y * spriteScale;

    ctx.save();
    ctx.translate(body.position.x, body.position.y);
    ctx.rotate(body.angle);
    ctx.translate(-cx, -cy);
    ctx.scale(spriteScale, spriteScale);

    if (style.fill) {
      ctx.fillStyle = style.fill;
      ctx.fill(path2d);
    }
    if (style.stroke && style.lineWidth > 0) {
      ctx.strokeStyle = style.stroke;
      ctx.lineWidth = style.lineWidth / spriteScale;
      ctx.stroke(path2d);
    }
    ctx.restore();
  }
}

/* ---------- Visibility + Loop ---------- */
let running = false, rafId = null;
let lastTs = performance.now();
let frameSkip = 0;

function startLoop() {
  if (running) return;
  running = true;
  lastTs = performance.now();
  rafId = requestAnimationFrame(tick);
}

function stopLoop() {
  running = false;
  if (rafId) cancelAnimationFrame(rafId);
  rafId = null;
}

/* IntersectionObserver jetzt nur noch zum PAUSIEREN nutzen */
if ("IntersectionObserver" in window) {
  const io = new IntersectionObserver((entries) => {
    for (const e of entries) {
      if (e.isIntersecting) {
        isInView = true;
        startLoop();
      } else {
        isInView = false;
        stopLoop();
      }
    }
  }, { root: null, rootMargin: "400px 0px", threshold: 0 });
  io.observe(document.querySelector(".matter-wrap") || matterContainer);
} else {
  isInView = true;
  startLoop();
}

document.addEventListener("visibilitychange", () => {
  if (document.hidden) {
    stopLoop();
  } else if (isInView) {
    startLoop();
  }
});

/* ---------- Resize (ResizeObserver) ---------- */
let lastCanvasW = matterContainer.clientWidth,
    lastCanvasH = matterContainer.clientHeight;

function updateWalls() {
  Body.setPosition(ground, Vector.create(
    matterContainer.clientWidth / 2,
    matterContainer.clientHeight + THICCNESS / 2
  ));
  Body.setVertices(ground, Bodies.rectangle(
    ground.position.x,
    ground.position.y,
    Math.max(27184, matterContainer.clientWidth * 3),
    THICCNESS,
    { isStatic: true }
  ).vertices);

  Body.setPosition(leftWall, Vector.create(
    -THICCNESS / 2,
    matterContainer.clientHeight / 2
  ));
  Body.setVertices(leftWall, Bodies.rectangle(
    leftWall.position.x,
    leftWall.position.y,
    THICCNESS,
    matterContainer.clientHeight * 5,
    { isStatic: true }
  ).vertices);

  Body.setPosition(rightWall, Vector.create(
    matterContainer.clientWidth + THICCNESS / 2,
    matterContainer.clientHeight / 2
  ));
  Body.setVertices(rightWall, Bodies.rectangle(
    rightWall.position.x,
    rightWall.position.y,
    THICCNESS,
    matterContainer.clientHeight * 5,
    { isStatic: true }
  ).vertices);

  Body.setPosition(ceiling, Vector.create(
    matterContainer.clientWidth / 2,
    -TOP_WALL_OFFSET - THICCNESS / 2
  ));
  Body.setVertices(ceiling, Bodies.rectangle(
    ceiling.position.x,
    ceiling.position.y,
    Math.max(27184, matterContainer.clientWidth * 3),
    THICCNESS,
    { isStatic: true }
  ).vertices);
}

function handleResize() {
  resizeSpriteCanvas();
  updateWalls();

  const newSpriteScale = currentScale();
  const scaleRatio = newSpriteScale / (prevSpriteScale || newSpriteScale);
  if (isFinite(scaleRatio) && Math.abs(scaleRatio - 1) > 0.001) {
    for (const body of dynamicBodies) Body.scale(body, scaleRatio, scaleRatio);
    prevSpriteScale = newSpriteScale;
  }
  spriteScale = newSpriteScale;

  for (const b of dynamicBodies) {
    if (b.isSleeping) b.isSleeping = false;
    Body.applyForce(b, b.position, { x: 0, y: Math.max(1e-6, 0.000002 * b.mass) });
  }
  lastCanvasW = matterContainer.clientWidth;
  lastCanvasH = matterContainer.clientHeight;
  drawSprites();
}

if ("ResizeObserver" in window) {
  const ro = new ResizeObserver(() => handleResize());
  ro.observe(matterContainer);
} else {
  let resizeTO = null;
  const schedule = () => {
    clearTimeout(resizeTO);
    resizeTO = setTimeout(handleResize, 80);
  };
  window.addEventListener("resize", schedule);
  if (window.visualViewport) {
    window.visualViewport.addEventListener("resize", schedule, { passive: true });
  }
  window.addEventListener("orientationchange", schedule);
}

/* ---------- Physik-Loop (semi-fixed) ---------- */
function physicsStep(dtMs) {
  const now = performance.now();
  const timeSinceLastScroll = now - lastScrollTimestamp;

  if (timeSinceLastScroll > SCROLL_BURST_TIMEOUT) {
    activeScrollBurst = false;
  }

  const decay = Math.exp(-dtMs / Math.max(60, SCROLL_TRIGGER.tauMs));
  liftEnergy *= decay;

  if (liftEnergy > 0.00001 && activeScrollBurst) {
    const dt = Math.max(0.001, dtMs / 1000);
    const g = engine.world.gravity.y * engine.world.gravity.scale;

    const burstFactor = Math.max(0.1, 1.0 - (timeSinceLastScroll / SCROLL_BURST_TIMEOUT));
    const aUp = SCROLL_TRIGGER.baseAccelPerEnergy * liftEnergy * burstFactor;
    const capA = Math.max(0.2, SCROLL_TRIGGER.capAccelPerSec) * dt;

    for (const body of dynamicBodies) {
      const biasA = SCROLL_TRIGGER.antiSagBias * g;
      const a = Math.min(aUp + biasA, capA);
      Body.applyForce(body, body.position, { x: 0, y: -a * body.mass });

      const jitter = (Math.random() - 0.5) * SCROLL_TRIGGER.angularJitter;
      Body.setAngularVelocity(body, body.angularVelocity + jitter);
    }
  }

  const ease = Math.max(0, Math.min(1, SCROLL_TRIGGER.easePerSec));
  if (ease > 0) {
    const dt = Math.max(0.001, dtMs / 1000);
    const damp = Math.exp(-ease * dt);
    for (const body of dynamicBodies) {
      body.velocity.x *= damp;
      body.velocity.y *= damp;
      body.angularVelocity *= damp;
    }
  }
}

function isDirty() {
  let dirty = false;
  for (const inst of instances) {
    const b = inst.body;
    const prev = lastPositions.get(b);
    if (!prev) {
      lastPositions.set(b, { x: b.position.x, y: b.position.y, a: b.angle });
      dirty = true;
      continue;
    }
    const dx = Math.abs(b.position.x - prev.x);
    const dy = Math.abs(b.position.y - prev.y);
    const da = Math.abs(b.angle - prev.a);
    if (dx > RENDER.MOVE_EPS_POS || dy > RENDER.MOVE_EPS_POS || da > RENDER.MOVE_EPS_ANG) {
      prev.x = b.position.x;
      prev.y = b.position.y;
      prev.a = b.angle;
      dirty = true;
    }
  }
  return dirty;
}

function tick(ts) {
  if (!running) return;
  const dtMs = Math.min(50, ts - lastTs);
  lastTs = ts;

  accumulatorMs += dtMs;
  let steps = 0;
  while (accumulatorMs >= FIXED_DT && steps < 4) {
    physicsStep(FIXED_DT);
    Engine.update(engine, FIXED_DT);
    accumulatorMs -= FIXED_DT;
    steps++;
  }

  const targetFrameMs = 1000 / RENDER.TARGET_FPS;
  frameSkip = (dtMs > targetFrameMs * 1.4) ? (frameSkip + 1) % 2 : 0;

  if (!frameSkip && isDirty()) {
    drawSprites();
  }

  rafId = requestAnimationFrame(tick);
}

/* ---------- Initialisierung (inkrementell + früher Loop-Start) ---------- */

function initMatter() {
  buildInstancesAsync(() => {
    // Bodies in die Welt
    Composite.add(engine.world, [ground, leftWall, rightWall, ceiling, ...dynamicBodies]);

    // Sleep-Tweaks nach kompletter Welt
    Composite.allBodies(engine.world).forEach(b => { b.sleepThreshold = 30; });

    layoutInstancesEvenly(instances);
    spriteScale = currentScale();
    prevSpriteScale = spriteScale;
    drawSprites();

    // Sicherstellen, dass der Loop gestartet ist, sobald etwas vorhanden ist
    isInView = true;
    startLoop();
  });
}

// DOM ist hier sehr wahrscheinlich schon verfügbar; sonst ggf. in DOMContentLoaded packen.
initMatter();

/* ---------- OffscreenCanvas + Worker (optional, unverändert) ---------- */
try {
  const supportsOffscreen = "OffscreenCanvas" in window && spriteCanvas.transferControlToOffscreen;
  if (supportsOffscreen) {
    // Platzhalter – Zeichen-Logik bleibt auf dem Main Thread,
    // da Path2D + DOM-Styles hier genutzt werden.
  }
} catch {
  /* ignorieren */
}
