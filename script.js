"use strict";

/* =========================================================
   Config
   ========================================================= */
const ROWS = 8;
const COLS = 8;
const TYPE_COUNT = 6;
const HIGHSCORE_KEY = "match3_highscore";

const SWAP_MS = 220;
const MATCH_MS = 280;
const FALL_MS = 320;
const SHUFFLE_MAX_ATTEMPTS = 100;
const START_BOOSTERS = { hammer: 2, rocket: 2, bomb: 1, rainbow: 1 };

/* =========================================================
   DOM references
   ========================================================= */
const boardEl = document.getElementById("board");
const popupLayer = document.getElementById("popupLayer");
const boardMessageEl = document.getElementById("boardMessage");
const scoreValueEl = document.getElementById("scoreValue");
const highscoreValueEl = document.getElementById("highscoreValue");
const questCountEl = document.getElementById("questCount");
const questIconEl = document.getElementById("questIcon");
const questProgressFillEl = document.getElementById("questProgressFill");
const questCompleteOverlay = document.getElementById("questCompleteOverlay");
const finalScoreEl = document.getElementById("finalScore");
const newRecordTag = document.getElementById("newRecordTag");
const btnNewQuest = document.getElementById("btnNewQuest");

const boosterButtons = {
  hammer: document.getElementById("btnHammer"),
  rocket: document.getElementById("btnRocket"),
  bomb: document.getElementById("btnBomb"),
  rainbow: document.getElementById("btnRainbow"),
};
const boosterCountEls = {
  hammer: document.getElementById("countHammer"),
  rocket: document.getElementById("countRocket"),
  bomb: document.getElementById("countBomb"),
  rainbow: document.getElementById("countRainbow"),
};

/* =========================================================
   State
   ========================================================= */
let grid = [];          // grid[r][c] = { type, r, c, el } | null
let tileSize = 44;
let score = 0;
let highscore = 0;
let quest = null;       // { type, target }
let questProgress = 0;
let questActive = false;
let boosters = { ...START_BOOSTERS };
let isAnimating = false;
let selectedBooster = null;
let tapSelection = null; // { r, c }
let pointerStart = null; // { r, c, x, y }

/* =========================================================
   Utilities
   ========================================================= */
function randInt(n) {
  return Math.floor(Math.random() * n);
}

function createEmptyBoard() {
  return Array.from({ length: ROWS }, () => Array(COLS).fill(null));
}

function typesMatrix() {
  const m = createEmptyBoard();
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      m[r][c] = grid[r][c] ? grid[r][c].type : null;
    }
  }
  return m;
}

function key(r, c) {
  return r + "," + c;
}

function parseKey(k) {
  const [r, c] = k.split(",").map(Number);
  return { r, c };
}

/* =========================================================
   Pure board logic (operates on plain type matrices)
   ========================================================= */
function wouldCreateMatch(m, r, c, type) {
  if (c >= 2 && m[r][c - 1] === type && m[r][c - 2] === type) return true;
  if (r >= 2 && m[r - 1][c] === type && m[r - 2][c] === type) return true;
  return false;
}

function findMatches(m) {
  const matched = new Set();

  for (let r = 0; r < ROWS; r++) {
    let runStart = 0;
    for (let c = 1; c <= COLS; c++) {
      const same = c < COLS && m[r][c] !== null && m[r][c] === m[r][runStart];
      if (!same) {
        const runLen = c - runStart;
        if (runLen >= 3 && m[r][runStart] !== null) {
          for (let k2 = runStart; k2 < c; k2++) matched.add(key(r, k2));
        }
        runStart = c;
      }
    }
  }

  for (let c = 0; c < COLS; c++) {
    let runStart = 0;
    for (let r = 1; r <= ROWS; r++) {
      const same = r < ROWS && m[r][c] !== null && m[r][c] === m[runStart][c];
      if (!same) {
        const runLen = r - runStart;
        if (runLen >= 3 && m[runStart][c] !== null) {
          for (let k2 = runStart; k2 < r; k2++) matched.add(key(k2, c));
        }
        runStart = r;
      }
    }
  }

  return matched;
}

function swapInMatrix(m, r1, c1, r2, c2) {
  const t = m[r1][c1];
  m[r1][c1] = m[r2][c2];
  m[r2][c2] = t;
}

function hasPossibleMoves(m) {
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (c + 1 < COLS) {
        swapInMatrix(m, r, c, r, c + 1);
        const found = findMatches(m).size > 0;
        swapInMatrix(m, r, c, r, c + 1);
        if (found) return true;
      }
      if (r + 1 < ROWS) {
        swapInMatrix(m, r, c, r + 1, c);
        const found = findMatches(m).size > 0;
        swapInMatrix(m, r, c, r + 1, c);
        if (found) return true;
      }
    }
  }
  return false;
}

function generateValidBoard() {
  let best = null;
  for (let attempt = 0; attempt < SHUFFLE_MAX_ATTEMPTS; attempt++) {
    const m = createEmptyBoard();
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        const candidates = [];
        for (let t = 0; t < TYPE_COUNT; t++) {
          if (!wouldCreateMatch(m, r, c, t)) candidates.push(t);
        }
        m[r][c] = candidates.length ? candidates[randInt(candidates.length)] : randInt(TYPE_COUNT);
      }
    }
    best = m;
    if (hasPossibleMoves(m)) return m;
  }
  // Deterministic fallback: should be practically unreachable, but guarantees
  // we never spin forever trying to find a valid layout.
  return best;
}

/* =========================================================
   Rendering / tile lifecycle
   ========================================================= */
function computeTileSize() {
  tileSize = boardEl.clientWidth / COLS;
  document.documentElement.style.setProperty("--tile-size", tileSize + "px");
}

function positionTile(tile, r, c, immediate) {
  tile.r = r;
  tile.c = c;
  tile.el.dataset.r = r;
  tile.el.dataset.c = c;
  if (immediate) {
    tile.el.style.transition = "none";
    tile.el.style.transform = `translate3d(${c * tileSize}px, ${r * tileSize}px, 0)`;
    void tile.el.offsetWidth; // force reflow
    tile.el.style.transition = "";
  } else {
    tile.el.style.transform = `translate3d(${c * tileSize}px, ${r * tileSize}px, 0)`;
  }
}

function createTile(type, r, c) {
  const el = document.createElement("div");
  el.className = `gem gem-${type}`;
  el.innerHTML = '<div class="gem-shape"></div>';
  boardEl.appendChild(el);
  const tile = { type, r, c, el };
  positionTile(tile, r, c, true);
  return tile;
}

function buildBoardFromMatrix(matrix) {
  boardEl.innerHTML = "";
  grid = createEmptyBoard();
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      const type = matrix[r][c];
      const spawnRow = r - ROWS - randInt(3);
      const tile = createTile(type, spawnRow, c);
      grid[r][c] = tile;
    }
  }
  requestAnimationFrame(() => {
    requestAnimationFrame(() => {
      for (let r = 0; r < ROWS; r++) {
        for (let c = 0; c < COLS; c++) {
          positionTile(grid[r][c], r, c, false);
        }
      }
    });
  });
}

function sleep(ms) {
  return new Promise((resolve) => setTimeout(resolve, ms));
}

/* =========================================================
   Score / quest / highscore UI
   ========================================================= */
function updateScoreDisplay() {
  scoreValueEl.textContent = String(score);
  scoreValueEl.classList.remove("bump");
  void scoreValueEl.offsetWidth;
  scoreValueEl.classList.add("bump");
}

function updateHighscoreDisplay() {
  highscoreValueEl.textContent = String(highscore);
}

function loadHighscore() {
  const raw = localStorage.getItem(HIGHSCORE_KEY);
  const val = raw ? parseInt(raw, 10) : 0;
  return Number.isFinite(val) ? val : 0;
}

function saveHighscoreIfNeeded() {
  if (score > highscore) {
    highscore = score;
    localStorage.setItem(HIGHSCORE_KEY, String(highscore));
    updateHighscoreDisplay();
    return true;
  }
  return false;
}

function generateQuest() {
  return {
    type: randInt(TYPE_COUNT),
    target: 20 + randInt(41), // 20 - 60
  };
}

function updateQuestUI() {
  questIconEl.innerHTML = "";
  const shape = document.createElement("div");
  shape.className = "gem-shape";
  const wrapper = document.createElement("div");
  wrapper.className = `gem gem-${quest.type}`;
  wrapper.style.position = "static";
  wrapper.style.width = "100%";
  wrapper.style.height = "100%";
  wrapper.appendChild(shape);
  questIconEl.appendChild(wrapper);

  questCountEl.textContent = `${Math.min(questProgress, quest.target)} / ${quest.target}`;
  const pct = Math.min(100, (questProgress / quest.target) * 100);
  questProgressFillEl.style.width = pct + "%";
  questProgressFillEl.classList.toggle("complete", questProgress >= quest.target);
}

function updateQuestProgress(removedByType) {
  if (!questActive || !quest) return;
  const got = removedByType[quest.type] || 0;
  if (got > 0) {
    questProgress = Math.min(quest.target, questProgress + got);
    updateQuestUI();
  }
}

function checkQuestComplete() {
  return questActive && quest && questProgress >= quest.target;
}

/* =========================================================
   Popups / feedback
   ========================================================= */
function showScorePopup(points, atR, atC) {
  const el = document.createElement("div");
  el.className = "score-popup";
  el.textContent = "+" + points;
  const x = (atC + 0.5) * tileSize;
  const y = atR * tileSize;
  el.style.left = x + "px";
  el.style.top = y + "px";
  el.style.transform = "translate(-50%, 0)";
  popupLayer.appendChild(el);
  setTimeout(() => el.remove(), 800);
}

function showComboBanner(chainLevel) {
  if (chainLevel < 2) return;
  const el = document.createElement("div");
  el.className = "combo-banner";
  el.textContent = `x${chainLevel} Combo!`;
  popupLayer.appendChild(el);
  setTimeout(() => el.remove(), 950);
}

function showBoardMessage(text, duration) {
  boardMessageEl.textContent = text;
  boardMessageEl.classList.add("show");
  return sleep(duration).then(() => {
    boardMessageEl.classList.remove("show");
  });
}

function spawnParticles(r, c, color) {
  const cx = (c + 0.5) * tileSize;
  const cy = (r + 0.5) * tileSize;
  const count = 5;
  for (let i = 0; i < count; i++) {
    const p = document.createElement("div");
    p.className = "particle";
    const angle = Math.random() * Math.PI * 2;
    const dist = 16 + Math.random() * 22;
    p.style.setProperty("--px", Math.cos(angle) * dist + "px");
    p.style.setProperty("--py", Math.sin(angle) * dist + "px");
    p.style.left = cx + "px";
    p.style.top = cy + "px";
    p.style.background = color;
    popupLayer.appendChild(p);
    setTimeout(() => p.remove(), 520);
  }
}

const TYPE_COLORS = [
  "var(--c-red)",
  "var(--c-blue)",
  "var(--c-green)",
  "var(--c-yellow)",
  "var(--c-purple)",
  "var(--c-orange)",
];

/* =========================================================
   Scoring
   ========================================================= */
function awardScore(cellsSet, chainLevel) {
  const count = cellsSet.size;
  let points = count * 10 + Math.max(0, count - 3) * 5;
  if (chainLevel > 1) {
    points = Math.round(points * (1 + (chainLevel - 1) * 0.5));
  }
  score += points;
  updateScoreDisplay();

  // popup near the centroid of the cleared cells
  let sumR = 0, sumC = 0;
  cellsSet.forEach((k) => {
    const { r, c } = parseKey(k);
    sumR += r; sumC += c;
  });
  const avgR = sumR / count;
  const avgC = sumC / count;
  showScorePopup(points, avgR, avgC);
  showComboBanner(chainLevel);
}

/* =========================================================
   Core resolve loop: clears matches, collapses, refills,
   repeats while new matches keep appearing (cascades).
   ========================================================= */
async function resolveBoard(initialCells) {
  isAnimating = true;
  updateBoosterUI();

  let chain = 0;
  let cellsToClear = initialCells || null;

  while (true) {
    if (!cellsToClear) {
      cellsToClear = findMatches(typesMatrix());
    }
    if (!cellsToClear || cellsToClear.size === 0) break;

    chain++;
    const removedByType = {};
    cellsToClear.forEach((k) => {
      const { r, c } = parseKey(k);
      const tile = grid[r][c];
      if (tile) removedByType[tile.type] = (removedByType[tile.type] || 0) + 1;
    });

    awardScore(cellsToClear, chain);
    updateQuestProgress(removedByType);

    await animateRemoveCells(cellsToClear);
    await collapseAndFill();

    if (checkQuestComplete()) {
      await sleep(150);
      await handleQuestComplete();
      isAnimating = false;
      updateBoosterUI();
      return;
    }

    cellsToClear = null; // next loop iteration looks for fresh cascade matches
  }

  if (!hasPossibleMoves(typesMatrix())) {
    await handleNoMoves();
  }

  isAnimating = false;
  updateBoosterUI();
}

async function animateRemoveCells(cellsSet) {
  cellsSet.forEach((k) => {
    const { r, c } = parseKey(k);
    const tile = grid[r][c];
    if (!tile) return;
    tile.el.classList.add("matched");
    spawnParticles(r, c, TYPE_COLORS[tile.type]);
  });
  await sleep(MATCH_MS);
  cellsSet.forEach((k) => {
    const { r, c } = parseKey(k);
    const tile = grid[r][c];
    if (!tile) return;
    tile.el.remove();
    grid[r][c] = null;
  });
}

async function collapseAndFill() {
  const newlyCreated = [];

  for (let c = 0; c < COLS; c++) {
    const stack = [];
    for (let r = ROWS - 1; r >= 0; r--) {
      if (grid[r][c]) stack.push(grid[r][c]);
    }
    for (let r = ROWS - 1, i = 0; r >= 0; r--, i++) {
      if (i < stack.length) {
        const tile = stack[i];
        grid[r][c] = tile;
        if (tile.r !== r) positionTile(tile, r, c, false);
      } else {
        grid[r][c] = null;
      }
    }
    const missing = ROWS - stack.length;
    for (let r = 0; r < missing; r++) {
      const type = randInt(TYPE_COUNT);
      const spawnRow = r - missing;
      const tile = createTile(type, spawnRow, c);
      grid[r][c] = tile;
      newlyCreated.push({ tile, finalR: r, finalC: c });
    }
  }

  if (newlyCreated.length) {
    await new Promise((resolve) => {
      requestAnimationFrame(() => {
        requestAnimationFrame(() => {
          newlyCreated.forEach(({ tile, finalR, finalC }) => {
            positionTile(tile, finalR, finalC, false);
          });
          resolve();
        });
      });
    });
  }

  await sleep(FALL_MS);
}

/* =========================================================
   Swap handling
   ========================================================= */
function areAdjacent(r1, c1, r2, c2) {
  const dr = Math.abs(r1 - r2);
  const dc = Math.abs(c1 - c2);
  return (dr === 1 && dc === 0) || (dr === 0 && dc === 1);
}

async function attemptSwap(a, b) {
  if (isAnimating) return;
  if (!areAdjacent(a.r, a.c, b.r, b.c)) return;

  isAnimating = true;
  updateBoosterUI();

  swapGridEntries(a, b);
  positionTile(grid[a.r][a.c], a.r, a.c, false);
  positionTile(grid[b.r][b.c], b.r, b.c, false);
  await sleep(SWAP_MS);

  const matches = findMatches(typesMatrix());
  if (matches.size > 0) {
    isAnimating = false; // resolveBoard will re-set this
    await resolveBoard(matches);
  } else {
    // swap back
    swapGridEntries(grid[a.r][a.c], grid[b.r][b.c]);
    positionTile(grid[a.r][a.c], a.r, a.c, false);
    positionTile(grid[b.r][b.c], b.r, b.c, false);
    await sleep(SWAP_MS);
    isAnimating = false;
    updateBoosterUI();
  }
}

function swapGridEntries(tileA, tileB) {
  const ra = tileA.r, ca = tileA.c;
  const rb = tileB.r, cb = tileB.c;
  grid[ra][ca] = tileB;
  grid[rb][cb] = tileA;
  tileA.r = rb; tileA.c = cb;
  tileB.r = ra; tileB.c = ca;
}

/* =========================================================
   No-moves handling
   ========================================================= */
async function handleNoMoves() {
  await showBoardMessage("Keine Zuege mehr \u2013 Brett wird neu gemischt!", 900);

  const tiles = [];
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (grid[r][c]) tiles.push(grid[r][c]);
    }
  }
  tiles.forEach((t) => (t.el.style.opacity = "0"));
  await sleep(220);
  boardEl.innerHTML = "";

  const matrix = generateValidBoard();
  buildBoardFromMatrix(matrix);
  await sleep(FALL_MS + 120);
}

/* =========================================================
   Boosters
   ========================================================= */
function updateBoosterUI() {
  Object.keys(boosters).forEach((k) => {
    boosterCountEls[k].textContent = String(boosters[k]);
    const btn = boosterButtons[k];
    btn.classList.toggle("active", selectedBooster === k);
    btn.classList.toggle("disabled", isAnimating || boosters[k] <= 0);
  });
  boardEl.classList.toggle("targeting", !!selectedBooster);
}

function toggleBooster(k) {
  if (isAnimating || boosters[k] <= 0) return;
  selectedBooster = selectedBooster === k ? null : k;
  tapSelection = null;
  clearTapHighlight();
  updateBoosterUI();
}

function applyBooster(kind, r, c, orientation) {
  if (isAnimating || boosters[kind] <= 0) return;
  if (!grid[r][c]) return;

  let cells = new Set();

  if (kind === "hammer") {
    cells.add(key(r, c));
  } else if (kind === "rocket") {
    if (orientation === "col") {
      for (let rr = 0; rr < ROWS; rr++) cells.add(key(rr, c));
    } else {
      for (let cc = 0; cc < COLS; cc++) cells.add(key(r, cc));
    }
  } else if (kind === "bomb") {
    for (let rr = r - 1; rr <= r + 1; rr++) {
      for (let cc = c - 1; cc <= c + 1; cc++) {
        if (rr >= 0 && rr < ROWS && cc >= 0 && cc < COLS) cells.add(key(rr, cc));
      }
    }
  } else if (kind === "rainbow") {
    const targetType = grid[r][c].type;
    for (let rr = 0; rr < ROWS; rr++) {
      for (let cc = 0; cc < COLS; cc++) {
        if (grid[rr][cc] && grid[rr][cc].type === targetType) cells.add(key(rr, cc));
      }
    }
  }

  boosters[kind]--;
  selectedBooster = null;
  tapSelection = null;
  clearTapHighlight();
  updateBoosterUI();

  resolveBoard(cells);
}

Object.keys(boosterButtons).forEach((k) => {
  boosterButtons[k].addEventListener("click", () => toggleBooster(k));
});

/* =========================================================
   Input handling (tap-tap and swipe, mouse + touch)
   ========================================================= */
function tileFromPoint(target) {
  const gemEl = target.closest ? target.closest(".gem") : null;
  if (!gemEl || !boardEl.contains(gemEl)) return null;
  const r = parseInt(gemEl.dataset.r, 10);
  const c = parseInt(gemEl.dataset.c, 10);
  if (Number.isNaN(r) || Number.isNaN(c)) return null;
  return { r, c };
}

function clearTapHighlight() {
  if (tapSelection && grid[tapSelection.r] && grid[tapSelection.r][tapSelection.c]) {
    grid[tapSelection.r][tapSelection.c].el.classList.remove("selected");
  }
}

function setTapHighlight(r, c) {
  clearTapHighlight();
  tapSelection = { r, c };
  if (grid[r][c]) grid[r][c].el.classList.add("selected");
}

function onPointerDown(e) {
  if (isAnimating) return;
  const pos = tileFromPoint(e.target);
  if (!pos) return;
  const point = e.touches ? e.touches[0] : e;
  pointerStart = { r: pos.r, c: pos.c, x: point.clientX, y: point.clientY };
}

function onPointerUp(e) {
  if (!pointerStart) return;
  if (isAnimating) { pointerStart = null; return; }

  const point = e.changedTouches ? e.changedTouches[0] : e;
  const dx = point.clientX - pointerStart.x;
  const dy = point.clientY - pointerStart.y;
  const absX = Math.abs(dx), absY = Math.abs(dy);
  const isSwipe = Math.max(absX, absY) > 18;

  const start = { r: pointerStart.r, c: pointerStart.c };
  pointerStart = null;

  if (selectedBooster) {
    handleBoosterInput(start, isSwipe, dx, dy);
    return;
  }

  if (isSwipe) {
    let target = null;
    if (absX > absY) {
      target = { r: start.r, c: start.c + (dx > 0 ? 1 : -1) };
    } else {
      target = { r: start.r + (dy > 0 ? 1 : -1), c: start.c };
    }
    if (target.r >= 0 && target.r < ROWS && target.c >= 0 && target.c < COLS) {
      clearTapHighlight();
      tapSelection = null;
      attemptSwap(start, target);
    }
    return;
  }

  // tap logic
  if (!tapSelection) {
    setTapHighlight(start.r, start.c);
    return;
  }
  if (tapSelection.r === start.r && tapSelection.c === start.c) {
    clearTapHighlight();
    tapSelection = null;
    return;
  }
  if (areAdjacent(tapSelection.r, tapSelection.c, start.r, start.c)) {
    const a = { r: tapSelection.r, c: tapSelection.c };
    clearTapHighlight();
    tapSelection = null;
    attemptSwap(a, start);
  } else {
    setTapHighlight(start.r, start.c);
  }
}

function handleBoosterInput(start, isSwipe, dx, dy) {
  const kind = selectedBooster;
  let orientation = "row";
  if (kind === "rocket" && isSwipe) {
    orientation = Math.abs(dx) > Math.abs(dy) ? "row" : "col";
  }
  applyBooster(kind, start.r, start.c, orientation);
}

boardEl.addEventListener("mousedown", onPointerDown);
window.addEventListener("mouseup", onPointerUp);
boardEl.addEventListener(
  "touchstart",
  (e) => {
    onPointerDown(e);
  },
  { passive: true }
);
boardEl.addEventListener(
  "touchmove",
  (e) => {
    if (pointerStart) e.preventDefault();
  },
  { passive: false }
);
boardEl.addEventListener("touchend", (e) => {
  onPointerUp(e);
});

/* =========================================================
   Quest completion / new round
   ========================================================= */
function hideQuestCompleteOverlay() {
  questCompleteOverlay.classList.add("hidden");
}

async function handleQuestComplete() {
  const isRecord = saveHighscoreIfNeeded();
  finalScoreEl.textContent = String(score);
  newRecordTag.classList.toggle("hidden", !isRecord);
  questCompleteOverlay.classList.remove("hidden");
}

function startNewRound() {
  hideQuestCompleteOverlay();
  selectedBooster = null;
  tapSelection = null;

  const matrix = generateValidBoard();
  buildBoardFromMatrix(matrix);

  score = 0;
  updateScoreDisplay();

  quest = generateQuest();
  questProgress = 0;
  questActive = true;
  updateQuestUI();

  boosters = { ...START_BOOSTERS };
  updateBoosterUI();
}

btnNewQuest.addEventListener("click", () => {
  startNewRound();
});

/* =========================================================
   Init
   ========================================================= */
function init() {
  highscore = loadHighscore();
  updateHighscoreDisplay();
  computeTileSize();
  startNewRound();

  window.addEventListener("resize", () => {
    computeTileSize();
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        if (grid[r][c]) positionTile(grid[r][c], r, c, true);
      }
    }
  });
}

init();
