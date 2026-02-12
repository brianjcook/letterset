const WORD_LIST_PATH = '_wordlists/unique-letter-words.txt';
const PUZZLES_PATH = 'puzzles.json';
const ROWS = 3;
const COLS = 5;
const UNUSUAL = new Set(['q', 'x', 'y', 'z']);
const MIN_SOLUTIONS = 3;

const state = {
  words: [],
  validSet: new Set(),
  tiles: [],
  grid: Array.from({ length: ROWS }, () => Array(COLS).fill('')),
  activeRow: 0,
  activeCol: 0,
  solved: false,
  dayKey: '',
  startTime: null,
  timerId: null
};

const bankEl = document.getElementById('letter-bank');
const gridEl = document.getElementById('word-grid');
const msgEl = document.getElementById('message');
const timerEl = document.getElementById('timer');
const countdownEl = document.getElementById('countdown');
const footerCountdownEl = document.getElementById('footer-countdown');
const footerCountdownTimeEl = document.getElementById('footer-countdown-time');
const modalTimeEl = document.getElementById('modal-time');

const submitBtn = document.getElementById('submit');
const resetBtn = document.getElementById('reset');
const nextPuzzleEl = document.getElementById('next-puzzle');
const modalEl = document.getElementById('success-modal');
const closeModalBtn = document.getElementById('close-modal');

function xmur3(str) {
  let h = 1779033703 ^ str.length;
  for (let i = 0; i < str.length; i++) {
    h = Math.imul(h ^ str.charCodeAt(i), 3432918353);
    h = (h << 13) | (h >>> 19);
  }
  return function () {
    h = Math.imul(h ^ (h >>> 16), 2246822507);
    h = Math.imul(h ^ (h >>> 13), 3266489909);
    return (h ^= h >>> 16) >>> 0;
  };
}

function mulberry32(a) {
  return function () {
    let t = (a += 0x6d2b79f5);
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function getEtParts(date = new Date()) {
  const fmt = new Intl.DateTimeFormat('en-US', {
    timeZone: 'America/New_York',
    year: 'numeric',
    month: '2-digit',
    day: '2-digit',
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hour12: false
  });
  const parts = fmt.formatToParts(date).reduce((acc, p) => {
    acc[p.type] = p.value;
    return acc;
  }, {});
  return {
    year: Number(parts.year),
    month: Number(parts.month),
    day: Number(parts.day),
    hour: Number(parts.hour),
    minute: Number(parts.minute),
    second: Number(parts.second)
  };
}

function getDayKey() {
  const parts = getEtParts();
  let { year, month, day, hour } = parts;
  if (hour < 3) {
    const d = new Date(Date.UTC(year, month - 1, day));
    d.setUTCDate(d.getUTCDate() - 1);
    year = d.getUTCFullYear();
    month = d.getUTCMonth() + 1;
    day = d.getUTCDate();
  }
  const mm = String(month).padStart(2, '0');
  const dd = String(day).padStart(2, '0');
  return `${year}-${mm}-${dd}`;
}

function getNextPuzzleTime() {
  const parts = getEtParts();
  const now = new Date();
  let next = new Date(Date.UTC(parts.year, parts.month - 1, parts.day));
  next = new Date(next.getTime() + 3 * 60 * 60 * 1000);
  if (parts.hour >= 3) {
    next = new Date(next.getTime() + 24 * 60 * 60 * 1000);
  }
  const diff = next.getTime() - now.getTime();
  return { next, diff };
}

function formatDuration(ms) {
  if (ms < 0) ms = 0;
  const total = Math.floor(ms / 1000);
  const h = String(Math.floor(total / 3600)).padStart(2, '0');
  const m = String(Math.floor((total % 3600) / 60)).padStart(2, '0');
  const s = String(total % 60).padStart(2, '0');
  return `${h}:${m}:${s}`;
}

function formatCountdownLong(ms) {
  if (ms < 0) ms = 0;
  const total = Math.floor(ms / 1000);
  const h = Math.floor(total / 3600);
  const m = Math.floor((total % 3600) / 60);
  const s = total % 60;
  return `${h} hours ${m} minutes ${s} seconds`;
}

function formatElapsedLong(totalSeconds) {
  const safeSeconds = Math.max(0, Math.floor(totalSeconds));
  const h = Math.floor(safeSeconds / 3600);
  const m = Math.floor((safeSeconds % 3600) / 60);
  const s = safeSeconds % 60;
  const parts = [];
  if (h > 0) parts.push(`${h} hours`);
  if (m > 0) parts.push(`${m} minutes`);
  if (s > 0 || parts.length === 0) parts.push(`${s} seconds`);
  if (parts.length === 1) return parts[0];
  if (parts.length === 2) return `${parts[0]} and ${parts[1]}`;
  return `${parts[0]} ${parts[1]} and ${parts[2]}`;
}

function shuffle(arr, rng) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

function computeMask(word) {
  let mask = 0;
  for (let i = 0; i < word.length; i++) {
    const bit = 1 << (word.charCodeAt(i) - 97);
    if (mask & bit) return null;
    mask |= bit;
  }
  return mask;
}

function countSolutionsForMask(fullMask, maskToCount, minSolutions) {
  const masks = [];
  for (const [mask] of maskToCount) {
    if ((mask & fullMask) === mask) masks.push(mask);
  }
  masks.sort((a, b) => a - b);
  let total = 0;
  for (let i = 0; i < masks.length; i++) {
    const m1 = masks[i];
    const c1 = maskToCount.get(m1) || 0;
    for (let j = i + 1; j < masks.length; j++) {
      const m2 = masks[j];
      if (m1 & m2) continue;
      const used = m1 | m2;
      if ((used & fullMask) !== used) continue;
      const m3 = fullMask ^ used;
      if (m3 <= m2) continue;
      const c3 = maskToCount.get(m3);
      if (!c3) continue;
      const c2 = maskToCount.get(m2) || 0;
      total += c1 * c2 * c3;
      if (total >= minSolutions) return total;
    }
  }
  return total;
}

function buildCandidates(allWords) {
  const candidates = [];
  const unusualCandidates = [];
  const maskToCount = new Map();
  for (const w of allWords) {
    const mask = computeMask(w);
    if (mask === null) continue;
    const unusualCount = w.split('').filter((ch) => UNUSUAL.has(ch)).length;
    const entry = { word: w, mask, unusualCount };
    candidates.push(entry);
    if (unusualCount > 0) unusualCandidates.push(entry);
    maskToCount.set(mask, (maskToCount.get(mask) || 0) + 1);
  }
  return { candidates, unusualCandidates, maskToCount };
}

function pickDailyWords(candidatesBundle, seed) {
  const rng = mulberry32(seed);
  const { candidates, unusualCandidates, maskToCount } = candidatesBundle;

  function tryFind(minUnusual) {
    for (let attempt = 0; attempt < 12000; attempt++) {
      const pool = unusualCandidates.length ? unusualCandidates : candidates;
      const start = pool[Math.floor(rng() * pool.length)];
      const pick = [start];
      let usedMask = start.mask;
      for (let slot = 1; slot < ROWS; slot++) {
        let found = null;
        for (let tries = 0; tries < 60; tries++) {
          const candidate = candidates[Math.floor(rng() * candidates.length)];
          if (candidate.mask & usedMask) continue;
          found = candidate;
          break;
        }
        if (!found) break;
        pick.push(found);
        usedMask |= found.mask;
      }
      if (pick.length === ROWS) {
        const totalUnusual = pick.reduce((sum, w) => sum + w.unusualCount, 0);
        if (totalUnusual < minUnusual) continue;
        let fullMask = 0;
        for (const entry of pick) fullMask |= entry.mask;
        const solutionCount = countSolutionsForMask(fullMask, maskToCount, MIN_SOLUTIONS);
        if (solutionCount >= MIN_SOLUTIONS) return pick;
      }
    }
    return null;
  }

  return tryFind(2) || tryFind(1) || tryFind(0);
}

function validatePuzzleWords(words, candidatesBundle) {
  if (!Array.isArray(words) || words.length !== ROWS) return false;
  const { maskToCount } = candidatesBundle;
  let fullMask = 0;
  for (const w of words) {
    const mask = computeMask(w);
    if (mask === null) return false;
    if (!maskToCount.has(mask)) return false;
    if (fullMask & mask) return false;
    fullMask |= mask;
  }
  const solutionCount = countSolutionsForMask(fullMask, maskToCount, MIN_SOLUTIONS);
  return solutionCount >= MIN_SOLUTIONS;
}

function buildTiles(words, seed) {
  const letters = words.join('').split('');
  const rng = mulberry32(seed ^ 0x9e3779b9);
  shuffle(letters, rng);
  state.tiles = letters.map((ch, idx) => ({ id: idx, ch, used: false }));
}

function renderBank() {
  bankEl.innerHTML = '';
  for (const tile of state.tiles) {
    const btn = document.createElement('button');
    btn.className = `letter-tile${tile.used ? ' used' : ''}`;
    btn.textContent = tile.ch.toUpperCase();
    btn.setAttribute('data-id', tile.id);
    btn.draggable = !tile.used;
    btn.addEventListener('click', () => placeFromTile(tile.id, null, null, true));
    btn.addEventListener('dragstart', (e) => {
      if (tile.used) return e.preventDefault();
      e.dataTransfer.setData('text/plain', tile.id);
    });
    bankEl.appendChild(btn);
  }
}

function renderGrid() {
  gridEl.innerHTML = '';
  for (let r = 0; r < ROWS; r++) {
    const row = document.createElement('div');
    row.className = 'word-row';
    for (let c = 0; c < COLS; c++) {
      const cell = document.createElement('div');
      cell.className = 'slot';
      if (r === state.activeRow && c === state.activeCol) cell.classList.add('active');
      cell.textContent = state.grid[r][c].toUpperCase();
      cell.setAttribute('data-row', r);
      cell.setAttribute('data-col', c);
      cell.addEventListener('click', () => {
        if (state.activeRow === r && state.activeCol === c && state.grid[r][c]) {
          removeAt(r, c);
        } else {
          setActive(r, c);
        }
      });
      cell.addEventListener('dragover', (e) => e.preventDefault());
      cell.addEventListener('drop', (e) => {
        e.preventDefault();
        const id = Number(e.dataTransfer.getData('text/plain'));
        placeFromTile(id, r, c);
      });
      row.appendChild(cell);
    }
    gridEl.appendChild(row);
  }
}

function setActive(row, col) {
  state.activeRow = row;
  state.activeCol = col;
  renderGrid();
}

function focusGrid() {
  if (gridEl.tabIndex < 0) gridEl.tabIndex = 0;
  gridEl.focus();
}

function focusFirstSlot() {
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (!state.grid[r][c]) {
        setActive(r, c);
        focusGrid();
        return;
      }
    }
  }
  setActive(0, 0);
  focusGrid();
}

function nextEmptyCell(row) {
  for (let c = 0; c < COLS; c++) {
    if (!state.grid[row][c]) return c;
  }
  return -1;
}

function nextOpenSlot(fromRow, fromCol) {
  for (let c = fromCol + 1; c < COLS; c++) {
    if (!state.grid[fromRow][c]) return { row: fromRow, col: c };
  }
  for (let r = fromRow + 1; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (!state.grid[r][c]) return { row: r, col: c };
    }
  }
  return null;
}

function placeFromTile(id, row = null, col = null, useActiveCol = false) {
  const tile = state.tiles.find((t) => t.id === id);
  if (!tile || state.solved) return;
  if (row === null) row = state.activeRow;
  if (col === null) col = useActiveCol ? state.activeCol : nextEmptyCell(row);
  if (col < 0) return;
  if (state.grid[row][col]) {
    releaseAt(row, col);
  }
  if (tile.used) {
    const { row: fromRow, col: fromCol } = findTilePosition(tile.ch);
    if (fromRow !== -1) {
      releaseAt(fromRow, fromCol);
    }
  }
  state.grid[row][col] = tile.ch;
  tile.used = true;
  const nextOpen = nextOpenSlot(row, col);
  if (nextOpen) {
    state.activeRow = nextOpen.row;
    state.activeCol = nextOpen.col;
  }
  persistState();
  renderBank();
  renderGrid();
  focusGrid();
}

function findTilePosition(ch) {
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      if (state.grid[r][c] === ch) return { row: r, col: c };
    }
  }
  return { row: -1, col: -1 };
}

function releaseAt(row, col) {
  const ch = state.grid[row][col];
  if (!ch) return;
  const tile = state.tiles.find((t) => t.ch === ch && t.used);
  if (tile) tile.used = false;
  state.grid[row][col] = '';
}

function removeAt(row, col) {
  if (!state.grid[row][col] || state.solved) return;
  releaseAt(row, col);
  setActive(row, col);
  persistState();
  renderBank();
  renderGrid();
}

function clearRow(row) {
  for (let c = 0; c < COLS; c++) {
    removeAt(row, c);
  }
}

function resetAll() {
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      state.grid[r][c] = '';
    }
  }
  state.tiles.forEach((t) => (t.used = false));
  state.solved = false;
  setMessage('');
  showNextPuzzle(false);
  closeModal();
  trackEvent('reset_all');
  persistState(true);
  renderBank();
  renderGrid();
}

function setMessage(text, type) {
  msgEl.textContent = text;
  msgEl.className = 'message';
  if (type) msgEl.classList.add(type);
}

function showNextPuzzle(show) {
  if (footerCountdownEl) footerCountdownEl.style.display = show ? 'block' : 'none';
}

function openModal() {
  if (!modalEl) return;
  modalEl.classList.add('open');
  modalEl.setAttribute('aria-hidden', 'false');
  trackEvent('modal_open');
}

function closeModal() {
  if (!modalEl) return;
  modalEl.classList.remove('open');
  modalEl.setAttribute('aria-hidden', 'true');
}

function validate() {
  const words = state.grid.map((row) => row.join(''));
  const hasEmpty = state.grid.flat().some((cell) => !cell);
  if (hasEmpty) {
    return { ok: false, reason: 'Fill all 15 letters before submitting.' };
  }
  const invalid = words.filter((w) => !state.validSet.has(w));
  if (invalid.length) {
    return { ok: false, reason: `Not in word list: ${invalid.map((w) => w.toUpperCase()).join(', ')}` };
  }
  const unused = state.tiles.filter((t) => !t.used);
  if (unused.length) {
    return { ok: false, reason: `Unused letters: ${unused.map((t) => t.ch.toUpperCase()).join(', ')}` };
  }
  return { ok: true };
}

function persistState(clear = false) {
  const key = `ls-state-${state.dayKey}`;
  if (clear) {
    localStorage.removeItem(key);
    return;
  }
  const payload = {
    grid: state.grid,
    tiles: state.tiles,
    solved: state.solved,
    startTime: state.startTime
  };
  localStorage.setItem(key, JSON.stringify(payload));
}

function restoreState() {
  const key = `ls-state-${state.dayKey}`;
  const data = localStorage.getItem(key);
  if (!data) return;
  try {
    const parsed = JSON.parse(data);
    if (parsed.grid && parsed.tiles) {
      state.grid = parsed.grid;
      state.tiles = parsed.tiles;
      state.solved = parsed.solved || false;
      state.startTime = parsed.startTime || state.startTime;
    }
  } catch (err) {
    console.warn('Failed to restore state', err);
  }
}

function initGridEvents() {
  gridEl.addEventListener('keydown', (e) => {
    const key = e.key.toLowerCase();
    if (key === 'backspace') {
      e.preventDefault();
      const { activeRow, activeCol } = state;
      if (state.grid[activeRow][activeCol]) {
        removeAt(activeRow, activeCol);
      }
      if (activeCol > 0) {
        setActive(activeRow, activeCol - 1);
      } else if (activeRow > 0) {
        setActive(activeRow - 1, COLS - 1);
      } else {
        setActive(activeRow, activeCol);
      }
      return;
    }
    if (key === 'arrowleft') {
      e.preventDefault();
      if (state.activeCol > 0) {
        setActive(state.activeRow, state.activeCol - 1);
      } else if (state.activeRow > 0) {
        setActive(state.activeRow - 1, COLS - 1);
      }
      return;
    }
    if (key === 'arrowright') {
      e.preventDefault();
      if (state.activeCol < COLS - 1) {
        setActive(state.activeRow, state.activeCol + 1);
      } else if (state.activeRow < ROWS - 1) {
        setActive(state.activeRow + 1, 0);
      }
      return;
    }
    if (key === 'arrowup') {
      e.preventDefault();
      if (state.activeRow > 0) setActive(state.activeRow - 1, state.activeCol);
      return;
    }
    if (key === 'arrowdown') {
      e.preventDefault();
      if (state.activeRow < ROWS - 1) setActive(state.activeRow + 1, state.activeCol);
      return;
    }
    if (!/^[a-z]$/.test(key)) return;
    const tile =
      state.tiles.find((t) => t.ch === key && !t.used) ||
      state.tiles.find((t) => t.ch === key);
    if (!tile) return;
    placeFromTile(tile.id, null, null, true);
  });
}

function setupButtons() {
  submitBtn.addEventListener('click', () => {
    const result = validate();
    if (result.ok) {
      state.solved = true;
      setMessage('Success! You found a solution.', 'success');
      showNextPuzzle(true);
      stopTimer();
      const elapsedSeconds = getElapsedSeconds();
      if (modalTimeEl) {
        modalTimeEl.textContent = `You found a solution in ${formatElapsedLong(elapsedSeconds)}.`;
      }
      trackEvent('submit_success', { elapsed_seconds: elapsedSeconds });
      openModal();
      persistState();
    } else {
      trackEvent('submit_failure', { reason: result.reason });
      setMessage(result.reason, 'error');
    }
    if (!state.solved) focusFirstSlot();
  });

  resetBtn.addEventListener('click', () => {
    resetAll();
    focusFirstSlot();
  });

  if (closeModalBtn) {
    closeModalBtn.addEventListener('click', closeModal);
  }

  if (modalEl) {
    modalEl.addEventListener('click', (e) => {
      if (e.target === modalEl) closeModal();
    });
  }
}

function startTimer() {
  if (!state.startTime) state.startTime = Date.now();
  if (state.timerId) return;
  state.timerId = setInterval(() => {
    const elapsed = Date.now() - state.startTime;
    timerEl.textContent = formatDuration(elapsed);
  }, 1000);
}

function stopTimer() {
  if (state.timerId) clearInterval(state.timerId);
  state.timerId = null;
}

function getElapsedSeconds() {
  if (!state.startTime) return 0;
  return Math.floor((Date.now() - state.startTime) / 1000);
}

function trackEvent(name, params = {}) {
  if (typeof window.gtag !== 'function') return;
  window.gtag('event', name, params);
}

function startCountdown() {
  function tick() {
    const { diff } = getNextPuzzleTime();
    countdownEl.textContent = formatDuration(diff);
    if (footerCountdownTimeEl) footerCountdownTimeEl.textContent = formatCountdownLong(diff);
  }
  tick();
  setInterval(tick, 1000);
}

async function init() {
  state.dayKey = getDayKey();
  const seed = xmur3(state.dayKey)();

  const response = await fetch(WORD_LIST_PATH);
  const text = await response.text();
  const words = text.split(/\r?\n/).map((w) => w.trim().toLowerCase()).filter(Boolean);
  state.words = words;
  state.validSet = new Set(words);
  const candidatesBundle = buildCandidates(words);

  let pickWords = null;
  try {
    const puzzlesRes = await fetch(PUZZLES_PATH);
    if (puzzlesRes.ok) {
      const puzzles = await puzzlesRes.json();
      const match = puzzles.puzzles?.find((p) => p.date === state.dayKey);
      if (match && Array.isArray(match.words) && match.words.length === ROWS) {
        if (validatePuzzleWords(match.words, candidatesBundle)) {
          pickWords = match.words;
        }
      }
    }
  } catch (err) {
    console.warn('Failed to load puzzles.json, falling back.', err);
  }

  if (!pickWords) {
    const pick = pickDailyWords(candidatesBundle, seed);
    if (!pick) {
      setMessage('Failed to build a puzzle. Refresh to try again.', 'error');
      return;
    }
    pickWords = pick.map((p) => p.word);
  }

  buildTiles(pickWords, seed);
  restoreState();

  renderBank();
  renderGrid();

  setupButtons();
  initGridEvents();
  startTimer();
  startCountdown();

  showNextPuzzle(state.solved);
  if (state.solved) {
    setMessage('Solved! Come back tomorrow for a new puzzle.', 'success');
    stopTimer();
    if (modalTimeEl) {
      modalTimeEl.textContent = `You found a solution in ${formatElapsedLong(getElapsedSeconds())}.`;
    }
  }

  trackEvent('puzzle_start', { day_key: state.dayKey });

  focusFirstSlot();
}

init();
