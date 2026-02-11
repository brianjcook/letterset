const WORD_LIST_PATH = '../valid-wordle-words.txt';
const PUZZLES_PATH = '../puzzles.json';
const ROWS = 3;
const MIN_DATE = '2026-02-10';

const statusEl = document.getElementById('status');
const listEl = document.getElementById('solutions-list');
const dateLabelEl = document.getElementById('date-label');
const lettersLabelEl = document.getElementById('letters-label');
const countLabelEl = document.getElementById('count-label');
const dateInputEl = document.getElementById('date-input');
const prevBtn = document.getElementById('prev-day');
const nextBtn = document.getElementById('next-day');

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
  return formatDateKey(year, month, day);
}

function formatDateKey(year, month, day) {
  const mm = String(month).padStart(2, '0');
  const dd = String(day).padStart(2, '0');
  return `${year}-${mm}-${dd}`;
}

function parseDateKey(key) {
  const [y, m, d] = key.split('-').map(Number);
  return { year: y, month: m, day: d };
}

function clampDateKey(key, minKey, maxKey) {
  if (key < minKey) return minKey;
  if (key > maxKey) return maxKey;
  return key;
}

function shiftDateKey(key, deltaDays) {
  const { year, month, day } = parseDateKey(key);
  const date = new Date(Date.UTC(year, month - 1, day));
  date.setUTCDate(date.getUTCDate() + deltaDays);
  return formatDateKey(date.getUTCFullYear(), date.getUTCMonth() + 1, date.getUTCDate());
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

function pickDailyWords(allWords, seed) {
  const rng = mulberry32(seed);
  const candidates = [];
  for (const w of allWords) {
    const mask = computeMask(w);
    if (mask === null) continue;
    candidates.push({ word: w, mask });
  }

  for (let attempt = 0; attempt < 12000; attempt++) {
    const start = candidates[Math.floor(rng() * candidates.length)];
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
    if (pick.length === ROWS) return pick;
  }
  return null;
}

async function loadWords() {
  const response = await fetch(WORD_LIST_PATH);
  const text = await response.text();
  return text
    .split(/\r?\n/)
    .map((w) => w.trim().toLowerCase())
    .filter(Boolean);
}

async function loadPuzzleMap() {
  try {
    const res = await fetch(PUZZLES_PATH);
    if (!res.ok) return new Map();
    const data = await res.json();
    const map = new Map();
    if (Array.isArray(data.puzzles)) {
      for (const entry of data.puzzles) {
        if (entry.date && Array.isArray(entry.words)) {
          map.set(entry.date, entry.words);
        }
      }
    }
    return map;
  } catch (err) {
    console.warn('Failed to load puzzles.json', err);
    return new Map();
  }
}

function computeSolutions(words, letters) {
  const poolMask = computeMask(letters);
  if (poolMask === null) return [];

  const candidates = [];
  const maskToIndices = new Map();

  for (let i = 0; i < words.length; i++) {
    const w = words[i];
    const mask = computeMask(w);
    if (mask === null) continue;
    if ((mask & poolMask) !== mask) continue;
    const entry = { word: w, mask };
    candidates.push(entry);
    if (!maskToIndices.has(mask)) maskToIndices.set(mask, []);
    maskToIndices.get(mask).push(candidates.length - 1);
  }

  const results = [];
  const fullMask = poolMask;
  for (let i = 0; i < candidates.length; i++) {
    const a = candidates[i];
    for (let j = i + 1; j < candidates.length; j++) {
      const b = candidates[j];
      if (a.mask & b.mask) continue;
      const used = a.mask | b.mask;
      const remMask = fullMask ^ used;
      if ((used & fullMask) !== used) continue;
      const remIndices = maskToIndices.get(remMask);
      if (!remIndices) continue;
      for (const k of remIndices) {
        if (k <= j) continue;
        const c = candidates[k];
        results.push([a.word, b.word, c.word]);
      }
    }
  }

  return results;
}

function renderSolutions(dateKey, letters, solutions) {
  dateLabelEl.textContent = dateKey;
  lettersLabelEl.textContent = letters.toUpperCase().split('').join(' ');
  countLabelEl.textContent = String(solutions.length);
  listEl.innerHTML = '';

  if (!solutions.length) {
    statusEl.textContent = 'No solutions found.';
    return;
  }

  statusEl.textContent = '';
  for (const set of solutions) {
    const li = document.createElement('li');
    li.textContent = set.map((w) => w.toUpperCase()).join(' / ');
    listEl.appendChild(li);
  }
}

function getRequestedDate(maxDateKey) {
  const params = new URLSearchParams(window.location.search);
  const requested = params.get('date');
  if (!requested) return maxDateKey;
  return clampDateKey(requested, MIN_DATE, maxDateKey);
}

function updateNavigation(dateKey, maxDateKey) {
  dateInputEl.min = MIN_DATE;
  dateInputEl.max = maxDateKey;
  dateInputEl.value = dateKey;
  prevBtn.disabled = dateKey <= MIN_DATE;
  nextBtn.disabled = dateKey >= maxDateKey;
}

function navigateTo(dateKey) {
  const url = new URL(window.location.href);
  url.searchParams.set('date', dateKey);
  window.location.href = url.toString();
}

async function init() {
  const maxDateKey = getDayKey();
  const requestedDate = getRequestedDate(maxDateKey);
  updateNavigation(requestedDate, maxDateKey);

  prevBtn.addEventListener('click', () => {
    navigateTo(shiftDateKey(requestedDate, -1));
  });
  nextBtn.addEventListener('click', () => {
    navigateTo(shiftDateKey(requestedDate, 1));
  });
  dateInputEl.addEventListener('change', () => {
    const value = clampDateKey(dateInputEl.value, MIN_DATE, maxDateKey);
    navigateTo(value);
  });

  const [words, puzzleMap] = await Promise.all([loadWords(), loadPuzzleMap()]);

  let puzzleWords = puzzleMap.get(requestedDate);
  if (!puzzleWords) {
    const seed = xmur3(requestedDate)();
    const pick = pickDailyWords(words, seed);
    puzzleWords = pick ? pick.map((p) => p.word) : null;
  }

  if (!puzzleWords) {
    statusEl.textContent = 'Could not determine puzzle for this date.';
    return;
  }

  const letters = puzzleWords.join('');
  const solutions = computeSolutions(words, letters);
  renderSolutions(requestedDate, letters, solutions);
}

init();
