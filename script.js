"use strict";

/* =========================================================
   Prisma Match
   Match-3 + cascades + special tiles + boosters
   ========================================================= */

const ROWS = 8;
const COLS = 8;
const TYPE_COUNT = 6;
const HIGHSCORE_KEY = "match3_highscore";

const SWAP_MS = 220;
const MATCH_MS = 280;
const FALL_MS = 320;
const SPECIAL_EFFECT_MS = 260;
const SHUFFLE_MAX_ATTEMPTS = 150;
const START_BOOSTERS = { hammer: 2, rocket: 2, bomb: 1, rainbow: 1 };

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

let grid = [];
let tileSize = 44;
let score = 0;
let highscore = 0;
let quest = null;
let questProgress = 0;
let questActive = false;
let boosters = { ...START_BOOSTERS };
let isAnimating = false;
let selectedBooster = null;
let tapSelection = null;
let pointerStart = null;

/* =========================================================
   Utilities
   ========================================================= */

function randInt(n) {
  return Math.floor(Math.random() * n);
}

function createEmptyBoard() {
  return Array.from({ length: ROWS }, () => Array(COLS).fill(null));
}

function key(r, c) {
  return `${r},${c}`;
}

function parseKey(k) {
  const [r, c] = k.split(",").map(Number);
  return { r, c };
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
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

function wouldCreateMatch(m, r, c, type) {
  if (c >= 2 && m[r][c - 1] === type && m[r][c - 2] === type) return true;
  if (r >= 2 && m[r - 1][c] === type && m[r - 2][c] === type) return true;
  return false;
}

/* =========================================================
   Pure board logic
   ========================================================= */

function findMatches(m) {
  const matched = new Set();

  // Horizontal
  for (let r = 0; r < ROWS; r++) {
    let start = 0;
    for (let c = 1; c <= COLS; c++) {
      const same = c < COLS && m[r][c] !== null && m[r][c] === m[r][start];
      if (!same) {
        const len = c - start;
        if (m[r][start] !== null && len >= 3) {
          for (let cc = start; cc < c; cc++) matched.add(key(r, cc));
        }
        start = c;
      }
    }
  }

  // Vertical
  for (let c = 0; c < COLS; c++) {
    let start = 0;
    for (let r = 1; r <= ROWS; r++) {
      const same = r < ROWS && m[r][c] !== null && m[r][c] === m[start][c];
      if (!same) {
        const len = r - start;
        if (m[start][c] !== null && len >= 3) {
          for (let rr = start; rr < r; rr++) matched.add(key(rr, c));
        }
        start = r;
      }
    }
  }

  return matched;
}

function getRuns(m) {
  const runs = [];

  for (let r = 0; r < ROWS; r++) {
    let start = 0;
    for (let c = 1; c <= COLS; c++) {
      const same = c < COLS && m[r][c] !== null && m[r][c] === m[r][start];
      if (!same) {
        const len = c - start;
        if (m[r][start] !== null && len >= 3) {
          const cells = [];
          for (let cc = start; cc < c; cc++) cells.push({ r, c: cc });
          runs.push({ orientation: "row", type: m[r][start], cells });
        }
        start = c;
      }
    }
  }

  for (let c = 0; c < COLS; c++) {
    let start = 0;
    for (let r = 1; r <= ROWS; r++) {
      const same = r < ROWS && m[r][c] !== null && m[r][c] === m[start][c];
      if (!same) {
        const len = r - start;
        if (m[start][c] !== null && len >= 3) {
          const cells = [];
          for (let rr = start; rr < r; rr++) cells.push({ r: rr, c });
          runs.push({ orientation: "col", type: m[start][c], cells });
        }
        start = r;
      }
    }
  }

  return runs;
}

function isLOrTIntersection(cells) {
  const set = new Set(cells.map(p => key(p.r, p.c)));
  const rowCounts = new Map();
  const colCounts = new Map();

  for (const p of cells) {
    rowCounts.set(p.r, (rowCounts.get(p.r) || 0) + 1);
    colCounts.set(p.c, (colCounts.get(p.c) || 0) + 1);
  }

  // Any intersection of a horizontal run and vertical run inside the
  // same matched component is enough for a bomb.
  for (const p of cells) {
    if ((rowCounts.get(p.r) || 0) >= 3 && (colCounts.get(p.c) || 0) >= 3) return true;
  }

  // Also catch compact L/T shapes that have one arm of 2.
  for (const p of cells) {
    let horizontal = 0;
    let vertical = 0;
    for (const q of cells) {
      if (q.r === p.r) horizontal++;
      if (q.c === p.c) vertical++;
    }
    if (horizontal >= 3 && vertical >= 2) return true;
    if (vertical >= 3 && horizontal >= 2) return true;
  }

  return false;
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
  for (let attempt = 0; attempt < SHUFFLE_MAX_ATTEMPTS; attempt++) {
    const m = createEmptyBoard();

    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        const candidates = [];
        for (let t = 0; t < TYPE_COUNT; t++) {
          if (!wouldCreateMatch(m, r, c, t)) candidates.push(t);
        }
        m[r][c] = candidates.length
          ? candidates[randInt(candidates.length)]
          : randInt(TYPE_COUNT);
      }
    }

    if (findMatches(m).size === 0 && hasPossibleMoves(m)) return m;
  }

  // Deterministic guaranteed fallback:
  // Build a checker-like pattern with one deliberate possible swap.
  const m = createEmptyBoard();
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      m[r][c] = (r * 2 + c) % TYPE_COUNT;
    }
  }

  // Force a legal horizontal move around row 0:
  // [0,1,0] -> swap positions 1 and 2 -> [0,0,1] is not enough,
  // so use [0,1,0,0] and swap 1/2 -> [0,0,1,0] still not enough.
  // Instead construct [1,0,1] then swap center with a 1.
  m[0][0] = 1;
  m[0][1] = 0;
  m[0][2] = 1;
  m[0][3] = 1;
  m[0][4] = 3;

  // Remove accidental matches from the rest by regenerate until valid.
  if (findMatches(m).size === 0 && hasPossibleMoves(m)) return m;

  // Guaranteed small pattern fallback search.
  for (let a = 0; a < TYPE_COUNT; a++) {
    for (let b = 0; b < TYPE_COUNT; b++) {
      for (let c = 0; c < TYPE_COUNT; c++) {
        if (a === b || b === c) continue;
        m[0][0] = a;
        m[0][1] = b;
        m[0][2] = a;
        m[0][3] = a;
        m[0][4] = c;
        if (findMatches(m).size === 0 && hasPossibleMoves(m)) return m;
      }
    }
  }

  // Extremely defensive: recurse with a fresh random attempt.
  return generateValidBoard();
}

/* =========================================================
   Tile rendering
   ========================================================= */

function computeTileSize() {
  tileSize = boardEl.clientWidth / COLS;
  document.documentElement.style.setProperty("--tile-size", tileSize + "px");
}

function specialClass(special) {
  if (!special) return "";
  return ` special special-${special}`;
}

function createTile(type, r, c, special = null) {
  const el = document.createElement("div");
  el.className = `gem gem-${type}${specialClass(special)}`;
  const icon = special === "rocket-row" ? "➜"
  : special === "rocket-col" ? "↑"
  : special === "bomb" ? "💣"
  : special === "rainbow" ? "🌈"
  : "";

el.innerHTML = `
  <div class="gem-shape">
    ${icon ? `<span class="special-icon">${icon}</span>` : ""}
  </div>
`;
  boardEl.appendChild(el);

  const tile = { type, r, c, el, special };
  positionTile(tile, r, c, true);
  return tile;
}

function updateTileAppearance(tile) {
  if (!tile || !tile.el) return;

  tile.el.className = `gem gem-${tile.type}${specialClass(tile.special)}`;

  const icon = tile.special === "rocket-row" ? "➜"
    : tile.special === "rocket-col" ? "↑"
    : tile.special === "bomb" ? "💣"
    : tile.special === "rainbow" ? "🌈"
    : "";

  tile.el.innerHTML = `
    <div class="gem-shape">
      ${icon ? `<span class="special-icon">${icon}</span>` : ""}
    </div>
  `;
}

function positionTile(tile, r, c, immediate = false) {
  if (!tile || !tile.el) return;

  tile.r = r;
  tile.c = c;
  tile.el.dataset.r = String(r);
  tile.el.dataset.c = String(c);

  if (immediate) {
    tile.el.style.transition = "none";
    tile.el.style.transform = `translate3d(${c * tileSize}px, ${r * tileSize}px, 0)`;
    void tile.el.offsetWidth;
    tile.el.style.transition = "";
  } else {
    tile.el.style.transform = `translate3d(${c * tileSize}px, ${r * tileSize}px, 0)`;
  }
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

/* =========================================================
   Score / quest
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
  try {
    const raw = localStorage.getItem(HIGHSCORE_KEY);
    const val = raw ? parseInt(raw, 10) : 0;
    return Number.isFinite(val) ? val : 0;
  } catch {
    return 0;
  }
}

function saveHighscoreIfNeeded() {
  if (score > highscore) {
    highscore = score;
    try {
      localStorage.setItem(HIGHSCORE_KEY, String(highscore));
    } catch {}
    updateHighscoreDisplay();
    return true;
  }
  return false;
}

function generateQuest() {
  return {
    type: randInt(TYPE_COUNT),
    target: 20 + randInt(41)
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
   Feedback
   ========================================================= */

const TYPE_COLORS = [
  "var(--c-red)", "var(--c-blue)", "var(--c-green)",
  "var(--c-yellow)", "var(--c-purple)", "var(--c-orange)"
];

function showScorePopup(points, atR, atC) {
  const el = document.createElement("div");
  el.className = "score-popup";
  el.textContent = "+" + points;
  el.style.left = ((atC + 0.5) * tileSize) + "px";
  el.style.top = (atR * tileSize) + "px";
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
  return sleep(duration).then(() => boardMessageEl.classList.remove("show"));
}

function spawnParticles(r, c, color, count = 5) {
  const cx = (c + 0.5) * tileSize;
  const cy = (r + 0.5) * tileSize;

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

/* =========================================================
   Scoring
   ========================================================= */

function awardScore(cellsSet, chainLevel, bonus = 0) {
  const count = cellsSet.size;
  let points = count * 10 + Math.max(0, count - 3) * 5;

  if (chainLevel > 1) {
    points = Math.round(points * (1 + (chainLevel - 1) * 0.5));
  }

  points += bonus;
  score += points;
  updateScoreDisplay();

  let sumR = 0, sumC = 0;
  cellsSet.forEach(k => {
    const { r, c } = parseKey(k);
    sumR += r;
    sumC += c;
  });

  showScorePopup(points, sumR / count, sumC / count);
  showComboBanner(chainLevel);
}

/* =========================================================
   Grid operations
   ========================================================= */

function swapGridEntries(tileA, tileB) {
  if (!tileA || !tileB) return;

  const ra = tileA.r, ca = tileA.c;
  const rb = tileB.r, cb = tileB.c;

  grid[ra][ca] = tileB;
  grid[rb][cb] = tileA;

  tileA.r = rb; tileA.c = cb;
  tileB.r = ra; tileB.c = ca;
}

function areAdjacent(r1, c1, r2, c2) {
  const dr = Math.abs(r1 - r2);
  const dc = Math.abs(c1 - c2);
  return (dr === 1 && dc === 0) || (dr === 0 && dc === 1);
}

/* =========================================================
   Special tile creation
   ========================================================= */

function chooseCreationCell(groupCells, swapInfo) {
  if (swapInfo) {
    const preferred = [swapInfo.to, swapInfo.from];
    for (const p of preferred) {
      if (p && groupCells.some(q => q.r === p.r && q.c === p.c)) return { ...p };
    }
  }

  const center = groupCells[Math.floor(groupCells.length / 2)];
  return { r: center.r, c: center.c };
}

function getSpecialCreations(matrix, matches, swapInfo) {
  const runs = getRuns(matrix);
  const creations = [];
  const occupiedCreationCells = new Set();

  // Build connected components of matched cells first. This lets us detect
  // L/T/cross shapes even when they are represented by two runs.
  const remaining = new Set(matches);
  const components = [];

  while (remaining.size) {
    const start = remaining.values().next().value;
    const queue = [parseKey(start)];
    remaining.delete(start);
    const cells = [];

    while (queue.length) {
      const p = queue.shift();
      cells.push(p);

      const neighbors = [
        { r: p.r - 1, c: p.c }, { r: p.r + 1, c: p.c },
        { r: p.r, c: p.c - 1 }, { r: p.r, c: p.c + 1 }
      ];

      for (const n of neighbors) {
        if (n.r < 0 || n.r >= ROWS || n.c < 0 || n.c >= COLS) continue;
        const k = key(n.r, n.c);
        if (remaining.has(k)) {
          remaining.delete(k);
          queue.push(n);
        }
      }
    }

    components.push(cells);
  }

  for (const cells of components) {
    const type = matrix[cells[0].r][cells[0].c];
    const componentRuns = runs.filter(run =>
      run.type === type &&
      run.cells.some(p => cells.some(q => q.r === p.r && q.c === p.c))
    );

    const maxRun = componentRuns.reduce((max, run) => Math.max(max, run.cells.length), 0);
    const hasFive = maxRun >= 5 || cells.length >= 5 && componentRuns.some(r => r.cells.length >= 5);
    const hasLT = isLOrTIntersection(cells);
    let special = null;

    if (hasFive) {
      special = "rainbow";
    } else if (hasLT) {
      special = "bomb";
    } else if (maxRun >= 4) {
      // Horizontal 4 -> row rocket, vertical 4 -> column rocket.
      const longest = componentRuns
        .filter(r => r.cells.length === maxRun)
        .sort((a, b) => a.orientation.localeCompare(b.orientation))[0];
      special = longest && longest.orientation === "col" ? "rocket-col" : "rocket-row";
    }

    if (!special) continue;

    const creation = chooseCreationCell(cells, swapInfo);
    const ck = key(creation.r, creation.c);

    if (!occupiedCreationCells.has(ck)) {
      creations.push({ ...creation, type, special });
      occupiedCreationCells.add(ck);
    }
  }

  return creations;
}

/* =========================================================
   Special effects
   ========================================================= */

function addRow(set, r) {
  for (let c = 0; c < COLS; c++) set.add(key(r, c));
}

function addCol(set, c) {
  for (let r = 0; r < ROWS; r++) set.add(key(r, c));
}

function addArea(set, centerR, centerC, radius) {
  for (let r = centerR - radius; r <= centerR + radius; r++) {
    for (let c = centerC - radius; c <= centerC + radius; c++) {
      if (r >= 0 && r < ROWS && c >= 0 && c < COLS) set.add(key(r, c));
    }
  }
}

function cellsForSpecial(tile) {
  const cells = new Set();

  if (!tile) return cells;

  if (tile.special === "rocket-row") {
    addRow(cells, tile.r);
  } else if (tile.special === "rocket-col") {
    addCol(cells, tile.c);
  } else if (tile.special === "bomb") {
    addArea(cells, tile.r, tile.c, 1);
  } else if (tile.special === "rainbow") {
    // Rainbow alone clears the type that is selected when it is activated.
    // The caller can override this with a target type.
  }

  return cells;
}

function cellsForSpecialWithTarget(tile, targetType = null) {
  if (!tile) return new Set();

  if (tile.special === "rainbow") {
    const cells = new Set();
    const type = targetType === null ? tile.type : targetType;
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) {
        if (grid[r][c] && grid[r][c].type === type) cells.add(key(r, c));
      }
    }
    return cells;
  }

  return cellsForSpecial(tile);
}

function getSpecialBonus(special) {
  if (special === "rocket-row" || special === "rocket-col") return 50;
  if (special === "bomb") return 60;
  if (special === "rainbow") return 100;
  return 0;
}

function collectSpecialChain(initialCells, rainbowTargetType = null) {
  const cellsToClear = new Set(initialCells);
  const processed = new Set();
  const queue = [...initialCells];

  while (queue.length) {
    const k = queue.shift();
    if (processed.has(k)) continue;
    processed.add(k);

    const { r, c } = parseKey(k);
    const tile = grid[r]?.[c];
    if (!tile || !tile.special) continue;

    let effect;

    if (tile.special === "rainbow") {
      effect = cellsForSpecialWithTarget(tile, rainbowTargetType);
    } else {
      effect = cellsForSpecial(tile);
    }

    for (const ek of effect) {
      if (!cellsToClear.has(ek)) {
        cellsToClear.add(ek);
        queue.push(ek);
      }
    }
  }

  return cellsToClear;
}

async function activateSpecialSwap(tileA, tileB) {
  if (!tileA || !tileB) return false;
  if (!tileA.special && !tileB.special) return false;

  // Rainbow + normal tile: target the normal tile's color.
  if (tileA.special === "rainbow" && !tileB.special) {
    const cells = cellsForSpecialWithTarget(tileA, tileB.type);
    await resolveBoard(cells, { specialBonus: 100 });
    return true;
  }

  if (tileB.special === "rainbow" && !tileA.special) {
    const cells = cellsForSpecialWithTarget(tileB, tileA.type);
    await resolveBoard(cells, { specialBonus: 100 });
    return true;
  }

  // Rainbow + Rainbow: clear the entire board.
  if (tileA.special === "rainbow" && tileB.special === "rainbow") {
    const cells = new Set();
    for (let r = 0; r < ROWS; r++) {
      for (let c = 0; c < COLS; c++) cells.add(key(r, c));
    }
    await resolveBoard(cells, { specialBonus: 200 });
    return true;
  }

  // Two non-rainbow specials.
  if (tileA.special && tileB.special) {
    const cells = new Set();

    const rocketA = tileA.special.startsWith("rocket");
    const rocketB = tileB.special.startsWith("rocket");
    const bombA = tileA.special === "bomb";
    const bombB = tileB.special === "bomb";

    if (rocketA && rocketB) {
      addRow(cells, tileA.r);
      addCol(cells, tileB.c);
      addRow(cells, tileB.r);
      addCol(cells, tileA.c);
    } else if ((rocketA && bombB) || (rocketB && bombA)) {
      const rocket = rocketA ? tileA : tileB;
      const bomb = bombA ? tileA : tileB;
      // Strong cross: 3 rows + 3 columns around the bomb/rocket area.
      for (let d = -1; d <= 1; d++) {
        const rr = Math.max(0, Math.min(ROWS - 1, bomb.r + d));
        const cc = Math.max(0, Math.min(COLS - 1, bomb.c + d));
        addRow(cells, rr);
        addCol(cells, cc);
      }
      addRow(cells, rocket.r);
      addCol(cells, rocket.c);
    } else if (bombA && bombB) {
      addArea(cells, tileA.r, tileA.c, 2);
      addArea(cells, tileB.r, tileB.c, 2);
    }

    cells.add(key(tileA.r, tileA.c));
    cells.add(key(tileB.r, tileB.c));

    await resolveBoard(cells, { specialBonus: 150 });
    return true;
  }

  // One special + normal tile: activating by swapping is allowed.
  const special = tileA.special ? tileA : tileB;
  const target = tileA.special ? tileB : tileA;
  let cells = cellsForSpecialWithTarget(special, target.type);
  if (special.special !== "rainbow") {
    cells = cellsForSpecial(special);
    cells.add(key(target.r, target.c));
  }

  await resolveBoard(cells, { specialBonus: getSpecialBonus(special.special) });
  return true;
}

/* =========================================================
   Removing / collapsing
   ========================================================= */

async function animateRemoveCells(cellsSet) {
  const valid = [];

  cellsSet.forEach(k => {
    const { r, c } = parseKey(k);
    const tile = grid[r]?.[c];
    if (!tile) return;

    valid.push({ k, tile, r, c });
    tile.el.classList.add("matched");
    spawnParticles(r, c, TYPE_COLORS[tile.type], tile.special ? 9 : 5);
  });

  await sleep(MATCH_MS);

  for (const item of valid) {
    const { r, c, tile } = item;
    if (grid[r]?.[c] === tile) {
      tile.el.remove();
      grid[r][c] = null;
    }
  }
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
        if (tile.r !== r || tile.c !== c) positionTile(tile, r, c, false);
      } else {
        grid[r][c] = null;
      }
    }

    const missing = ROWS - stack.length;

    for (let r = 0; r < missing; r++) {
      const type = randInt(TYPE_COUNT);
      const spawnRow = r - missing - randInt(2);
      const tile = createTile(type, spawnRow, c);
      grid[r][c] = tile;
      newlyCreated.push({ tile, finalR: r, finalC: c });
    }
  }

  if (newlyCreated.length) {
    await new Promise(resolve => {
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
   Main resolve loop
   ========================================================= */

async function resolveBoard(initialCells = null, options = {}) {
  if (isAnimating) {
    // resolveBoard is only called internally while already locked,
    // except for booster/special entry points.
  }

  isAnimating = true;
  updateBoosterUI();

  let chain = 0;
  let cellsToClear = initialCells ? new Set(initialCells) : null;
  let swapInfo = options.swapInfo || null;
  let specialBonus = options.specialBonus || 0;

  while (true) {
    if (!cellsToClear) {
      cellsToClear = findMatches(typesMatrix());
    }

    if (!cellsToClear || cellsToClear.size === 0) break;

    // If this is a normal match, determine whether it should create a special.
    const matrixBeforeClear = typesMatrix();
    const normalMatches = findMatches(matrixBeforeClear);

    // For explicit booster/special effects, don't create a new special.
    const isNormalMatchResolution = !initialCells || chain > 0;
    let creations = [];

    if (chain === 0 && (!initialCells || options.allowSpecialCreation !== false)) {
      // Only create specials for cells produced by a normal swap.
      if (normalMatches.size > 0 && swapInfo) {
        creations = getSpecialCreations(matrixBeforeClear, normalMatches, swapInfo);
      }
    }

    // Expand explicit effects if they contain special tiles.
    if (initialCells || chain > 0) {
      cellsToClear = collectSpecialChain(cellsToClear);
    }

    chain++;

    const removedByType = {};
    let specialBonusThisRound = specialBonus;
    const creationKeys = new Set(creations.map(c => key(c.r, c.c)));

    cellsToClear.forEach(k => {
      const { r, c } = parseKey(k);
      const tile = grid[r]?.[c];
      if (!tile) return;

      // A creation cell is preserved and transformed into the special tile.
      if (creationKeys.has(k)) return;

      removedByType[tile.type] = (removedByType[tile.type] || 0) + 1;
      if (tile.special) specialBonusThisRound += getSpecialBonus(tile.special);
    });

    // If we are creating specials, the creation tile counts as collected too:
    // it remains on the board, so it should not advance the quest.
    awardScore(cellsToClear, chain, specialBonusThisRound);
    updateQuestProgress(removedByType);

    await animateRemoveCells(new Set(
      [...cellsToClear].filter(k => !creationKeys.has(k))
    ));

    // Create specials exactly where selected before collapse.
    for (const creation of creations) {
      const existing = grid[creation.r]?.[creation.c];

      if (existing) {
        existing.type = creation.type;
        existing.special = creation.special;
        updateTileAppearance(existing);
        existing.el.classList.remove("matched");
        spawnParticles(creation.r, creation.c, "#ffffff", 8);
      } else {
        const tile = createTile(creation.type, creation.r, creation.c, creation.special);
        grid[creation.r][creation.c] = tile;
      }
    }

    await sleep(60);
    await collapseAndFill();

    if (checkQuestComplete()) {
      await sleep(150);
      await handleQuestComplete();
      isAnimating = false;
      updateBoosterUI();
      return;
    }

    // Cascades: find newly created matches.
    cellsToClear = findMatches(typesMatrix());
    swapInfo = null;
    specialBonus = 0;

    // If a cascade contains a special tile, activate it as part of the cascade.
    if (cellsToClear.size > 0) {
      cellsToClear = collectSpecialChain(cellsToClear);
    }
  }

  if (!hasPossibleMoves(typesMatrix())) {
    await handleNoMoves();
  }

  isAnimating = false;
  updateBoosterUI();
}

/* =========================================================
   Swapping
   ========================================================= */

async function attemptSwap(a, b) {
  if (isAnimating) return;
  if (!areAdjacent(a.r, a.c, b.r, b.c)) return;

  const tileA = grid[a.r]?.[a.c];
  const tileB = grid[b.r]?.[b.c];
  if (!tileA || !tileB) return;

  isAnimating = true;
  updateBoosterUI();

  // IMPORTANT:
  // Keep the original coordinates before changing tile.r/tile.c.
  // The visual swap happens FIRST. Only after SWAP_MS do we inspect matches.
  const from = { r: a.r, c: a.c };
  const to = { r: b.r, c: b.c };

  swapGridEntries(tileA, tileB);

  positionTile(tileA, to.r, to.c, false);
  positionTile(tileB, from.r, from.c, false);

  // Wait until the player has actually seen the swap.
  await sleep(SWAP_MS);

  // Special + anything activates even when the swap itself creates no normal match.
  if (tileA.special || tileB.special) {
    await activateSpecialSwap(tileA, tileB);
    isAnimating = false;
    updateBoosterUI();
    return;
  }

  const matches = findMatches(typesMatrix());

  if (matches.size > 0) {
    await resolveBoard(matches, {
      swapInfo: { from, to },
      allowSpecialCreation: true
    });
  } else {
    // Illegal swap: visually reverse the same two tiles.
    swapGridEntries(tileA, tileB);
    positionTile(tileA, from.r, from.c, false);
    positionTile(tileB, to.r, to.c, false);

    await sleep(SWAP_MS);

    isAnimating = false;
    updateBoosterUI();
  }
}

/* =========================================================
   No moves / shuffle
   ========================================================= */

async function handleNoMoves() {
  await showBoardMessage("Keine Züge mehr – Brett wird neu gemischt!", 650);

  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      const tile = grid[r][c];
      if (tile) {
        tile.el.style.transition = "transform .22s ease, opacity .22s ease";
        tile.el.style.opacity = "0";
        tile.el.style.transform += " scale(.7)";
      }
    }
  }

  await sleep(240);

  const matrix = generateValidBoard();
  buildBoardFromMatrix(matrix);

  await sleep(FALL_MS + 140);
}

/* =========================================================
   Manual boosters
   ========================================================= */

function updateBoosterUI() {
  Object.keys(boosters).forEach(k => {
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

async function applyBooster(kind, r, c, orientation = "row") {
  if (isAnimating || boosters[kind] <= 0) return;
  if (!grid[r]?.[c]) return;

  const cells = new Set();

  if (kind === "hammer") {
    cells.add(key(r, c));
  } else if (kind === "rocket") {
    orientation === "col" ? addCol(cells, c) : addRow(cells, r);
  } else if (kind === "bomb") {
    addArea(cells, r, c, 1);
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

  await resolveBoard(cells, { specialBonus: getSpecialBonus(kind === "rocket" ? "rocket-row" : kind) });
}

Object.keys(boosterButtons).forEach(k => {
  boosterButtons[k].addEventListener("click", () => toggleBooster(k));
});

/* =========================================================
   Input
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
  if (tapSelection && grid[tapSelection.r]?.[tapSelection.c]) {
    grid[tapSelection.r][tapSelection.c].el.classList.remove("selected");
  }
}

function setTapHighlight(r, c) {
  clearTapHighlight();
  tapSelection = { r, c };
  if (grid[r]?.[c]) grid[r][c].el.classList.add("selected");
}

function onPointerDown(e) {
  if (isAnimating) return;

  const pos = tileFromPoint(e.target);
  if (!pos) return;

  const point = e.touches ? e.touches[0] : e;
  pointerStart = {
    r: pos.r,
    c: pos.c,
    x: point.clientX,
    y: point.clientY
  };
}

function onPointerUp(e) {
  if (!pointerStart) return;

  if (isAnimating) {
    pointerStart = null;
    return;
  }

  const point = e.changedTouches ? e.changedTouches[0] : e;
  const dx = point.clientX - pointerStart.x;
  const dy = point.clientY - pointerStart.y;
  const absX = Math.abs(dx);
  const absY = Math.abs(dy);
  const isSwipe = Math.max(absX, absY) > 18;

  const start = { r: pointerStart.r, c: pointerStart.c };
  pointerStart = null;

  if (selectedBooster) {
    handleBoosterInput(start, isSwipe, dx, dy);
    return;
  }

  if (isSwipe) {
    let target;

    if (absX > absY) {
      target = { r: start.r, c: start.c + (dx > 0 ? 1 : -1) };
    } else {
      target = { r: start.r + (dy > 0 ? 1 : -1), c: start.c };
    }

    if (target.r >= 0 && target.r < ROWS && target.c >= 0 && target.c < COLS) {
      clearTapHighlight();
      tapSelection = null;
      void attemptSwap(start, target);
    }

    return;
  }

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
    void attemptSwap(a, start);
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

  void applyBooster(kind, start.r, start.c, orientation);
}

boardEl.addEventListener("mousedown", onPointerDown);
window.addEventListener("mouseup", onPointerUp);

boardEl.addEventListener("touchstart", onPointerDown, { passive: true });
boardEl.addEventListener("touchmove", e => {
  if (pointerStart) e.preventDefault();
}, { passive: false });
boardEl.addEventListener("touchend", onPointerUp);

/* =========================================================
   Quest completion
   ========================================================= */

function hideQuestCompleteOverlay() {
  questCompleteOverlay.classList.add("hidden");
}

async function handleQuestComplete() {
  questActive = false;

  const isRecord = saveHighscoreIfNeeded();
  finalScoreEl.textContent = String(score);
  newRecordTag.classList.toggle("hidden", !isRecord);
  questCompleteOverlay.classList.remove("hidden");
}

function startNewRound() {
  hideQuestCompleteOverlay();

  selectedBooster = null;
  tapSelection = null;
  pointerStart = null;

  score = 0;
  updateScoreDisplay();

  quest = generateQuest();
  questProgress = 0;
  questActive = true;
  updateQuestUI();

  boosters = { ...START_BOOSTERS };
  updateBoosterUI();

  const matrix = generateValidBoard();
  buildBoardFromMatrix(matrix);
}

btnNewQuest.addEventListener("click", () => {
  if (isAnimating) return;
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
