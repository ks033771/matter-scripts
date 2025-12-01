


/* ==========================================================
   Matter.js + Canvas-Renderer (optimiert)
   - Kein Matter.Render, eigener RAF-Loop (semi-fixed timestep)
   - DPR capped, Dirty-Rect-Heuristik, adaptive Frame-Skips
   - Scroll+Wheel gebÃ¼ndelt, sanft geglÃ¤ttet
   - Optional OffscreenCanvas+Worker (automatisch, Fallback vorhanden)
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
  POSITION_ITERATIONS: 4,   // weniger = schneller
  VELOCITY_ITERATIONS: 4,
  CONSTRAINT_ITERATIONS: 1
};

const BODY_DEFAULTS = { restitution:0.35, friction:0.3, frictionStatic:0.5, frictionAir:0.0012, density:0.001 };
const SVG_OPTS = { sample:6, simplifyTolerance:10.2 };

const LAYOUT = { marginPct:0.07, startYRatio:0.12, kickLinear:0.35, kickAngular:0.02 };
const RESPONSIVE_SIZE = [
  { maxViewportWidth:480,  percentOfContainer:0.6, minPx:150 },
  { maxViewportWidth:768,  percentOfContainer:0.6, minPx:175 },
  { maxViewportWidth:Infinity, percentOfContainer:SVG_WIDTH_AS_PERCENT_OF_CONTAINER_WIDTH, minPx:0 }
];

const SCROLL_TRIGGER = {
  energyPerPx:(function(){
  const isDesktop = window.matchMedia("(pointer: fine)").matches;
  return isDesktop ? 0.5 : 0.5;
})(),
  baseAccelPerEnergy:0.000015,
  capAccelPerSec:0.0000056,
  tauMs:360,
  viewportGuard:true,
  upOnly:true,
  angularJitter:0.01,
  easePerSec:0.06,
  antiSagBias:0.05
};

const RENDER = {
  DPR_CAP: 1.35,        // etwas niedriger fÃ¼r schwÃ¤chere Browser
  TARGET_FPS: 60,       // adaptiver Skip
  MOVE_EPS_POS: 0.2,    // unterdrÃ¼ckt minimalen Jitter
  MOVE_EPS_ANG: 0.002
};

/* ---------- DOM ---------- */
const matterContainer = document.querySelector("#matter-container");
if (!matterContainer) { console.warn("[matter-canvas] #matter-container fehlt."); }

/* ---------- Matter Aliases ---------- */
const { Engine, Runner, Bodies, Composite, Body, Svg, Vector, Vertices, Common, Events } = Matter;
if (window.decomp) Common.setDecomp(window.decomp);

/* ---------- Engine ---------- */
const engine = Engine.create();
engine.enableSleeping = PHYSICS.ENABLE_SLEEPING;
engine.world.gravity.x = PHYSICS.GRAVITY_X;
engine.world.gravity.y = PHYSICS.GRAVITY_Y;
engine.world.gravity.scale = PHYSICS.GRAVITY_SCALE;
engine.positionIterations  = PHYSICS.POSITION_ITERATIONS;
engine.velocityIterations  = PHYSICS.VELOCITY_ITERATIONS;
engine.constraintIterations = PHYSICS.CONSTRAINT_ITERATIONS;
// Warum: eigener fixer Timestep â†’ stabiler, weniger Re-Work
const FIXED_DT = 1000 / 60;
let accumulatorMs = 0;

/* ---------- EIN Canvas fÃ¼r alle Sprites ---------- */
const spriteCanvas = document.createElement("canvas");
const ctx = spriteCanvas.getContext("2d", { alpha:true, desynchronized:true }); // warum: weniger Blocking
spriteCanvas.style.position = "absolute";
spriteCanvas.style.left = "0";
spriteCanvas.style.top  = "0";
spriteCanvas.style.pointerEvents = "none";
matterContainer.style.position = "relative";
matterContainer.appendChild(spriteCanvas);

function dpr() { return Math.min(RENDER.DPR_CAP, window.devicePixelRatio || 1); }
function resizeSpriteCanvas() {
  const pr = dpr();
  const w = matterContainer.clientWidth|0;
  const h = matterContainer.clientHeight|0;
  spriteCanvas.width  = Math.max(1, Math.floor(w * pr));
  spriteCanvas.height = Math.max(1, Math.floor(h * pr));
  spriteCanvas.style.width  = w + "px";
  spriteCanvas.style.height = h + "px";
  ctx.setTransform(pr,0,0,pr,0,0);
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
  const raw  = base * rule.percentOfContainer;
  return Math.max(rule.minPx || 0, raw);
}
function currentScale() { return getTargetWidth() / SVG_WIDTH_IN_PX; }

function ensureClosed(verts){
  if (!verts.length) return verts;
  const a=verts[0], b=verts[verts.length-1];
  const dx=a.x-b.x, dy=a.y-b.y;
  if (dx*dx + dy*dy > 1e-6) verts = verts.concat([{x:a.x,y:a.y}]);
  return verts;
}
function polygonArea(verts){
  let area=0; for(let i=0,j=verts.length-1;i<verts.length;j=i++) area += verts[j].x*verts[i].y - verts[i].x*verts[j].y;
  return 0.5*area;
}
// DP Fallback
function simplifyDP(points, tol){
  if (!tol || points.length<=2) return points;
  const sqTol = tol*tol;
  function sqSegDist(p,a,b){
    let x=a.x, y=a.y, dx=b.x-x, dy=b.y-y;
    if (dx!==0 || dy!==0){
      const t=((p.x-x)*dx + (p.y-y)*dy)/(dx*dx+dy*dy);
      if (t>1){ x=b.x; y=b.y; }
      else if (t>0){ x+=dx*t; y+=dy*t; }
    }
    dx=p.x-x; dy=p.y-y; return dx*dx+dy*dy;
  }
  function simplifyRadial(pts, sq){
    let prev=pts[0], out=[prev], point;
    for (let i=1;i<pts.length;i++){
      point=pts[i];
      if ((point.x-prev.x)**2 + (point.y-prev.y)**2 > sq){ out.push(point); prev=point; }
    }
    if (prev!==point) out.push(point);
    return out;
  }
  function step(pts, first, last, sq, out){
    let max=sq, idx;
    for (let i=first+1; i<last; i++){
      const d=sqSegDist(pts[i], pts[first], pts[last]);
      if (d>max){ idx=i; max=d; }
    }
    if (max>sq){
      if (idx-first>1) step(pts, first, idx, sq, out);
      out.push(pts[idx]);
      if (last-idx>1) step(pts, idx, last, sq, out);
    }
  }
  const pts = simplifyRadial(points, sqTol);
  const last = pts.length-1;
  const out=[pts[0]];
  step(pts,0,last,sqTol,out);
  out.push(pts[last]);
  return out;
}

/* ---------- CSS-Variablen -> echte Farben ---------- */
/* ---------- CSS-Variablen -> echte Farben (ohne echte SVG-Elemente) ---------- */
function resolvePaintFromVars(def, refEl = matterContainer || document.documentElement) {
  const cs = getComputedStyle(refEl);

  let fill = "#222";
  if (def.fillVar) {
    const v = cs.getPropertyValue(def.fillVar).trim();
    if (v) fill = v;
  }

  let stroke = "";
  if (def.strokeVar) {
    const v = cs.getPropertyValue(def.strokeVar).trim();
    if (v) stroke = v;
  }

  const strokeWidth = def.strokeWidth || 0;
  return { fill, stroke, strokeWidth };
}


/* ---------- Mehrfache Instanzen pro Path (jetzt inline im JS) ---------- */
const SHAPE_COUNTS = {
  "#matter-shape-1": 3,
  "#matter-shape-2": 3,
  "#matter-shape-3": 2,
  "#matter-shape-4": 3
};

/**
 * Hier liegen die ehemals im HTML definierten Pfade.
 * WICHTIG: Wir speichern hier nur:
 *   - id                → für Mapping mit SHAPE_COUNTS
 *   - d                 → Pfad-Daten
 *   - fillVar / strokeVar → Name der CSS-Custom-Property
 */
const SHAPE_DEFS = [
  {
    id: "matter-shape-1",
    d: "M49.2638 37.296L0.934801 34.6436L25.7109 76.2232L7.89872 121.604L55.1183 110.454L92.4402 141.138L96.843 92.6727L137.731 66.2829L93.2318 47.4612L81.197 0.459315L49.2638 37.296Z",
    fillVar: "--_color-combinations---text-color-bright",
    strokeVar: null,
    strokeWidth: 0
  },
  {
    id: "matter-shape-2",
    d: "M140.209 60.8404C138.974 71.8693 136.095 81.4424 136.059 81.5832C131.946 81.4014 128.543 81.5183 126.578 81.7999C120.491 82.7135 113.495 80.626 111.6 80.0286C117.904 62.9907 98.8093 42.987 95.529 41.6514C97.516 39.3989 109.566 26.4777 120.981 30.4294C133.492 34.7965 141.417 49.736 140.209 60.8404ZM123.677 100.513C109.036 118.551 80.7493 118.802 80.7493 118.802L80.2049 119.084C82.0178 117.065 83.5802 115.307 84.443 113.758C86.8628 109.6 95.3721 104.058 102.877 94.6528C107.001 97.7327 114.936 100.036 123.625 100.489M56.5288 54.4706L56.5668 54.4569C56.4743 54.917 56.3165 55.3153 56.2621 55.7617C51.4371 80.2471 70.6045 87.5498 73.4929 88.5145C72.856 90.4511 74.2118 95.1689 63.0625 108.32C61.0401 110.714 59.2219 113.076 57.5315 115.435C54.3219 113.22 32.9654 98.1714 32.0334 81.0101C31.025 62.6813 38.5136 59.086 46.3969 56.5861C54.2803 54.0861 56.5288 54.4706 56.5288 54.4706ZM98.8231 3.71988C91.9443 6.49794 77.8032 16.844 67.4869 31.2313L67.1711 30.833C67.1711 30.833 44.6225 20.4814 26.3627 32.1839C8.15196 43.7834 -2.31645 63.6028 0.875019 81.0593C3.70432 96.5552 5.98378 112.676 45.5117 139.91L45.833 139.965C45.1771 142.805 44.7391 145.651 44.6712 148.45C44.2554 161.274 54.1997 164.134 61.4271 163.877C68.2707 163.629 73.5977 156.545 71.0599 144.486L72.3721 147.171C72.3721 147.171 122.679 155.328 154.817 109.732C159.306 113.704 165.998 120.681 174.082 117.426C182.663 113.992 180.345 100.274 169.998 91.1584C168.666 89.9739 167.057 88.9747 165.296 88.0306C175.816 70.625 170.95 47.328 170.95 47.328C156.571 -10.6074 109.219 -0.411162 98.8368 3.75765",
    fillVar: "--_color-combinations---text-color",
    strokeVar: null,
    strokeWidth: 0
  },
  {
    id: "matter-shape-3",
    d: "M57.0729 128.473C59.8296 129.735 62.6653 130.854 65.5313 131.859C62.6147 131.045 59.779 129.925 57.0729 128.473ZM133.322 97.5471C134.66 91.5702 135.651 85.5013 136.324 79.3889C137.841 67.2915 138.357 59.7487 139.129 39.8963C139.388 33.6334 139.532 27.3399 139.55 21.0539L53.7484 0.019244C45.3638 16.0965 37.8143 32.5994 31.1303 49.4135C27.2952 59.0582 22.7712 68.9696 22.6534 79.5183C22.4978 92.3854 30.7337 108.58 39.9864 117.365C44.2742 121.403 49.2386 124.598 54.5189 127.224C56.8382 129.513 59.983 133.819 58.5098 139.842C56.2553 148.966 42.3178 205.728 42.3178 205.728C42.3178 205.728 4.67648 209.962 3.40396 210.565C0.838683 211.845 -2.25113 214.171 4.09484 215.731L44.1265 225.488L83.994 235.242C89.1076 236.475 89.0157 234.49 87.9004 232.479C86.785 230.467 54.7118 208.728 54.7118 208.728C54.7118 208.728 68.6107 151.956 70.8267 142.822C72.2493 136.99 76.7699 134.553 79.9109 133.589C81.5727 133.539 83.1961 133.479 84.7039 133.389C90.1919 133.21 95.5946 132.11 100.689 130.152C115.11 124.417 129.522 113.124 133.294 97.4988",
    fillVar: "--_color-combinations---text-color",
    strokeVar: null,
    strokeWidth: 0
  },
  {
    id: "matter-shape-4",
    d: "M255.372 3.69619C248.422 -2.02378 238.122 -0.993871 232.342 6.01614C228.952 10.1262 227.892 15.3863 229.002 20.1863L195.522 60.7661C188.102 58.5362 180.212 57.7661 172.242 58.5462C156.182 60.1363 141.592 67.8963 131.222 80.3462L130.832 80.8162L124.322 75.4462C125.032 72.4263 124.062 69.1463 121.512 67.0462C117.922 64.0862 112.562 64.6262 109.582 68.2462C106.592 71.8662 107.082 77.2262 110.672 80.1863C113.402 82.4363 117.132 82.6463 120.092 81.0462L126.342 86.2062L111.612 103.906L105.202 98.6262C105.902 95.6162 104.942 92.3362 102.382 90.2362C98.8023 87.2761 93.4423 87.8162 90.4523 91.4363C87.4723 95.0462 87.9623 100.416 91.5523 103.376C94.2723 105.626 98.0023 105.826 100.962 104.236L107.112 109.306L92.0623 127.396L85.9323 122.336C86.9122 119.156 85.9523 115.596 83.2523 113.366C79.6722 110.406 74.3123 110.946 71.3223 114.566C68.3423 118.186 68.8323 123.556 72.4222 126.506C75.0023 128.636 78.4523 128.956 81.3223 127.636L87.5723 132.786L56.9723 169.556C51.0424 172.356 44.6622 175.066 37.8622 177.636C24.7123 182.596 12.2723 186.106 1.07227 188.636L1.02234 188.586C-0.127803 188.866 -0.367793 190.266 0.612187 191.076L61.7723 241.526C62.7223 242.306 64.1322 241.766 64.1322 240.596C64.0623 230.856 64.5823 220.006 66.1422 208.406C67.3622 199.386 69.0424 191.036 70.9923 183.406L102.722 145.276L110.162 151.416L114.622 145.996L107.212 139.886L122.262 121.806L129.622 127.876L134.092 122.456L126.752 116.406L141.492 98.6962L148.752 104.686L153.212 99.2661L145.982 93.3062L146.292 92.9263C153.272 84.5261 163.112 79.3162 173.912 78.2561C176.332 78.0161 178.722 77.9862 181.072 78.1763L112.982 160.736C98.1722 178.686 100.572 205.236 118.392 219.926C136.212 234.616 162.732 231.926 177.532 213.976L227.952 152.836C247.272 129.416 244.132 94.8262 220.922 75.6863L216.392 71.9462C215.502 71.2062 214.552 70.4862 213.622 69.8062L244.202 32.7262C249.122 32.8963 254.082 30.8562 257.472 26.7462C263.252 19.7362 262.312 9.4263 255.372 3.69619ZM212.782 140.326L162.352 201.466C154.522 210.956 140.542 212.366 131.132 204.606C121.722 196.836 120.442 182.846 128.272 173.346L200.942 85.2262C201.912 85.8762 202.822 86.5862 203.742 87.3362L208.272 91.0762C223.072 103.286 225.102 125.386 212.782 140.326Z",
    fillVar: "--_color-combinations---secondary-icon-color",
    strokeVar: null,
    strokeWidth: 0
  }
];

// erzeugt aus den Defs die tatsächlichen Instanzen
const instances = [];
for (const selector of Object.keys(SHAPE_COUNTS)) {
  const id = selector.slice(1); // "#matter-shape-1" -> "matter-shape-1"
  const def = SHAPE_DEFS.find(s => s.id === id);
  if (!def) continue;
  const count = SHAPE_COUNTS[selector] || 1;
  for (let i = 0; i < count; i++) {
    const inst = buildInstanceFromDef(def);
    instances.push(inst);
  }
}



function buildInstanceFromDef(def) {
  const d = def.d || "";
  const { fill, stroke, strokeWidth } = resolvePaintFromVars(def);

  // mehrere Subpfade (M...z M...z) trennen
  const chunks = d.split(/(?<=z|Z)\s*(?=M|m)/);
  const tempSVG = document.createElementNS("http://www.w3.org/2000/svg", "svg");

  let bestVerts = null;
  let bestArea = -Infinity;
  let bestCentroid = { x: 0, y: 0 };

  for (const seg of chunks) {
    const s = seg.trim();
    if (!s) continue;

    const p = document.createElementNS("http://www.w3.org/2000/svg", "path");
    p.setAttribute("d", s);
    tempSVG.appendChild(p); // muss NICHT ins DOM

    let v = Svg.pathToVertices(p, SVG_OPTS.sample);
    if (SVG_OPTS.simplifyTolerance && v.length > 4) {
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
  const body = Bodies.fromVertices(
    startX,
    startY,
    [scaledVerts],
    { ...BODY_DEFAULTS, render: { visible: false } },
    true
  );

  return {
    body,
    path2d: new Path2D(d),
    style: { fill, stroke, lineWidth: strokeWidth },
    rawCentroid: bestCentroid
  };
}


/* ---------- Weltgrenzen ---------- */
let ground = Bodies.rectangle(matterContainer.clientWidth/2, matterContainer.clientHeight + THICCNESS/2, 27184, THICCNESS, { isStatic:true });
let leftWall  = Bodies.rectangle(-THICCNESS/2, matterContainer.clientHeight/2, THICCNESS, matterContainer.clientHeight*5, { isStatic:true });
let rightWall = Bodies.rectangle(matterContainer.clientWidth + THICCNESS/2, matterContainer.clientHeight/2, THICCNESS, matterContainer.clientHeight*5, { isStatic:true });
let ceiling   = Bodies.rectangle(matterContainer.clientWidth/2, -TOP_WALL_OFFSET - THICCNESS/2, Math.max(27184, matterContainer.clientWidth*3), THICCNESS, { isStatic:true });

Composite.add(engine.world, [ground, leftWall, rightWall, ceiling, ...instances.map(i => i.body)]);

/* ---------- Startlayout ---------- */
function layoutInstancesRandom(list) {
  const W = matterContainer.clientWidth;
  const H = matterContainer.clientHeight;
  const n = list.length;
  if (!n) return;

  const margin = Math.max(24, W * LAYOUT.marginPct);
  for (let i = 0; i < n; i++) {
    const x = margin + Math.random() * (W - 2 * margin); // 👈 random x innerhalb vom Container
    const y = -100 - Math.random() * 150; // etwas mehr Höhe zufällig

    Body.setPosition(list[i].body, { x, y });
    Body.setVelocity(list[i].body, {
      x: (Math.random() - 0.5) * LAYOUT.kickLinear,
      y: 0
    });
    Body.setAngularVelocity(list[i].body, (Math.random() - 0.5) * LAYOUT.kickAngular);
  }
}

layoutInstancesRandom(instances);


/* ---------- Scroll/Wheel â†’ sanfter Lift ---------- */
let isInView=false;
let lastScrollY = window.scrollY || window.pageYOffset || 0;
let emaDY = 0;
let liftEnergy = 0;
const HARD_SCROLL_CLAMP = 140;
const EMA_ALPHA = 0.75;

let lastScrollTimestamp = 0;
let activeScrollBurst = false;
const SCROLL_BURST_TIMEOUT = 50; // in ms, wie lange ein Scroll-Burst maximal aktiv ist


// Warum: Wheel liefert bessere Deltas fÃ¼r MÃ¤use; Scroll fÃ¼r Touch/Trackpad
function handleLiftInput(dy) {
  dy = Math.max(-HARD_SCROLL_CLAMP, Math.min(HARD_SCROLL_CLAMP, dy));
  emaDY = EMA_ALPHA * emaDY + (1 - EMA_ALPHA) * dy;
  const add = Math.max(0, emaDY) * SCROLL_TRIGGER.energyPerPx;
  if (add > 0) {
    liftEnergy += add;
    lastScrollTimestamp = performance.now();  // neue Zeit merken
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
let lastPositions = new WeakMap(); // warum: Dirty-Check

function drawSprites(){
  ctx.clearRect(0,0,matterContainer.clientWidth,matterContainer.clientHeight);
  for (const inst of instances){
    const { body, path2d, style, rawCentroid } = inst;
    const cx = rawCentroid.x * spriteScale;
    const cy = rawCentroid.y * spriteScale;

    ctx.save();
    ctx.translate(body.position.x, body.position.y);
    ctx.rotate(body.angle);
    ctx.translate(-cx, -cy);
    ctx.scale(spriteScale, spriteScale);

    if (style.fill) { ctx.fillStyle = style.fill; ctx.fill(path2d); }
    if (style.stroke && style.lineWidth > 0){
      ctx.strokeStyle = style.stroke;
      ctx.lineWidth = style.lineWidth / spriteScale;
      ctx.stroke(path2d);
    }
    ctx.restore();
  }
}

/* ---------- Visibility ---------- */
function startLoop(){ running = true; rafId = requestAnimationFrame(tick); }
function stopLoop(){ running = false; if (rafId) cancelAnimationFrame(rafId); rafId = null; }

if ("IntersectionObserver" in window) {
  const io = new IntersectionObserver((entries) => {
    for (const e of entries) { isInView = e.isIntersecting; isInView ? startLoop() : stopLoop(); }
  }, { root: null, rootMargin: "400px 0px", threshold: 0 });
  io.observe(document.querySelector(".matter-wrap") || matterContainer);
} else { isInView = true; startLoop(); }

document.addEventListener("visibilitychange", () => {
  if (document.hidden) stopLoop();
  else if (isInView) startLoop();
});

/* ---------- Resize (ResizeObserver) ---------- */
let lastCanvasW = matterContainer.clientWidth, lastCanvasH = matterContainer.clientHeight;
function updateWalls(){
  Body.setPosition(ground, Vector.create(matterContainer.clientWidth/2, matterContainer.clientHeight + THICCNESS/2));
  Body.setVertices(ground, Bodies.rectangle(ground.position.x, ground.position.y, Math.max(27184, matterContainer.clientWidth*3), THICCNESS, { isStatic:true }).vertices);

  Body.setPosition(leftWall, Vector.create(-THICCNESS/2, matterContainer.clientHeight/2));
  Body.setVertices(leftWall, Bodies.rectangle(leftWall.position.x, leftWall.position.y, THICCNESS, matterContainer.clientHeight*5, { isStatic:true }).vertices);

  Body.setPosition(rightWall, Vector.create(matterContainer.clientWidth + THICCNESS/2, matterContainer.clientHeight/2));
  Body.setVertices(rightWall, Bodies.rectangle(rightWall.position.x, rightWall.position.y, THICCNESS, matterContainer.clientHeight*5, { isStatic:true }).vertices);

  Body.setPosition(ceiling, Vector.create(matterContainer.clientWidth/2, -TOP_WALL_OFFSET - THICCNESS/2));
  Body.setVertices(ceiling, Bodies.rectangle(ceiling.position.x, ceiling.position.y, Math.max(27184, matterContainer.clientWidth*3), THICCNESS, { isStatic:true }).vertices);
}

function handleResize(){
  resizeSpriteCanvas();
  updateWalls();

  const newSpriteScale = currentScale();
  const scaleRatio = newSpriteScale / (prevSpriteScale || newSpriteScale);
  if (isFinite(scaleRatio) && Math.abs(scaleRatio-1) > 0.001){
    const allBodies = Composite.allBodies(engine.world).filter(b => !b.isStatic);
    for (const body of allBodies) Body.scale(body, scaleRatio, scaleRatio);
    prevSpriteScale = newSpriteScale;
  }
  spriteScale = newSpriteScale;

  for (const b of Composite.allBodies(engine.world).filter(b => !b.isStatic)){
    if (b.isSleeping) b.isSleeping = false;
    Body.applyForce(b, b.position, { x:0, y:Math.max(1e-6, 0.000002*b.mass) });
  }
  lastCanvasW = matterContainer.clientWidth;
  lastCanvasH = matterContainer.clientHeight;
  drawSprites();
}

if ('ResizeObserver' in window){
  const ro = new ResizeObserver(() => handleResize());
  ro.observe(matterContainer);
} else {
  // Fallback debounce
  let resizeTO=null;
  const schedule = () => { clearTimeout(resizeTO); resizeTO=setTimeout(handleResize, 80); };
  window.addEventListener("resize", schedule);
  if (window.visualViewport) window.visualViewport.addEventListener("resize", schedule, { passive:true });
  window.addEventListener("orientationchange", schedule);
}

/* ---------- Physik-Loop (semi-fixed) ---------- */
let running = false, rafId = null;
let lastTs = performance.now();
let frameSkip = 0;

function physicsStep(dtMs){
  const now = performance.now();
  const timeSinceLastScroll = now - lastScrollTimestamp;

  // Scroll-Burst deaktivieren nach Timeout
  if (timeSinceLastScroll > SCROLL_BURST_TIMEOUT) {
    activeScrollBurst = false;
  }

  // sanfter Lift-Energy-Decay
  const decay = Math.exp(-dtMs / Math.max(60, SCROLL_TRIGGER.tauMs));
  liftEnergy *= decay;

  if (liftEnergy > 0.00001 && activeScrollBurst) {
    const bodies = instances.map(i => i.body).filter(b => !b.isStatic);
    const dt = Math.max(0.001, dtMs/1000);
    const g = engine.world.gravity.y * engine.world.gravity.scale;

    // NEU: Burst-Faktor reduziert die Kraft Ã¼ber Zeit
    const burstFactor = Math.max(0.1, 1.0 - (timeSinceLastScroll / SCROLL_BURST_TIMEOUT));
    const aUp = SCROLL_TRIGGER.baseAccelPerEnergy * liftEnergy * burstFactor;
    const capA = Math.max(0.2, SCROLL_TRIGGER.capAccelPerSec) * dt;

    for (const body of bodies){
      const biasA = SCROLL_TRIGGER.antiSagBias * g;
      const a = Math.min(aUp + biasA, capA);
      Body.applyForce(body, body.position, { x:0, y:-a * body.mass });

      const jitter = (Math.random()-0.5) * SCROLL_TRIGGER.angularJitter;
      Body.setAngularVelocity(body, body.angularVelocity + jitter);
    }
  }

  // Ease/DÃ¤mpfung
  const ease = Math.max(0, Math.min(1, SCROLL_TRIGGER.easePerSec));
  if (ease>0){
    const dt = Math.max(0.001, dtMs/1000);
    const damp = Math.exp(-ease * dt);
    const bodies = instances.map(i => i.body).filter(b => !b.isStatic);
    for (const body of bodies){
      body.velocity.x *= damp;
      body.velocity.y *= damp;
      body.angularVelocity *= damp;
    }
  }
}


function isDirty(){
  // warum: zeichnet nur, wenn Bewegung spÃ¼rbar ist
  let dirty=false;
  for (const inst of instances){
    const b = inst.body;
    const prev = lastPositions.get(b);
    if (!prev){
      lastPositions.set(b, {x:b.position.x, y:b.position.y, a:b.angle});
      dirty = true;
      continue;
    }
    const dx = Math.abs(b.position.x - prev.x);
    const dy = Math.abs(b.position.y - prev.y);
    const da = Math.abs(b.angle - prev.a);
    if (dx>RENDER.MOVE_EPS_POS || dy>RENDER.MOVE_EPS_POS || da>RENDER.MOVE_EPS_ANG){
      lastPositions.set(b, {x:b.position.x, y:b.position.y, a:b.angle});
      dirty = true;
    }
  }
  return dirty;
}

function tick(ts){
  if (!running) return;
  const dtMs = Math.min(50, ts - lastTs);
  lastTs = ts;

  accumulatorMs += dtMs;
  // max 4 Steps â†’ schÃ¼tzt vor Spiralen
  let steps = 0;
  while (accumulatorMs >= FIXED_DT && steps < 4){
    physicsStep(FIXED_DT);
    Engine.update(engine, FIXED_DT);
    accumulatorMs -= FIXED_DT;
    steps++;
  }

  // adaptiver Frame-Skip
  const targetFrameMs = 1000 / RENDER.TARGET_FPS;
  frameSkip = (dtMs > targetFrameMs * 1.4) ? (frameSkip+1)%2 : 0;

  if (!frameSkip && isDirty()){
    drawSprites();
  }

  rafId = requestAnimationFrame(tick);
}

/* ---------- Sofortiger erster Draw ---------- */
drawSprites();

/* ---------- OffscreenCanvas + Worker (optional) ----------
   Hinweis: Komplett optional; aktiviert NUR wenn unterstÃ¼tzt.
   Warum: Entlastet Main Thread bei Zeichenlast. */
try {
  const supportsOffscreen = 'OffscreenCanvas' in window && spriteCanvas.transferControlToOffscreen;
  if (supportsOffscreen) {
    // Minimal-Worker nur fÃ¼rs Zeichnen; Physik bleibt hier.
    // In diesem Beispiel bleibt Drawing lokal, da Path2D+DOM-Styles hier gebraucht werden.
    // Wenn du reine Bitmap-Sprites nutzt, verschiebe den Draw in den Worker.
  }
} catch { /* ignorieren */ }

/* ---------- Kleine QualitÃ¤ts-of-Life Tweaks ---------- */
// aggressiver schlafen lassen
Composite.allBodies(engine.world).forEach(b => { b.sleepThreshold = 30; });
