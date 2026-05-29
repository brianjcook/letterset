const WORD_LIST_PATH = '../_wordlists/unique-letter-words.txt';
const PUZZLES_PATH = '../puzzles.json';
const ROWS = 3;
const MIN_DATE = '2026-02-10';
const UNUSUAL = new Set(['q', 'x', 'y', 'z']);
const MIN_SOLUTIONS = 3;

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

function countSolutionsForMask(fullMask, maskToCount, minSolutions = Infinity) {
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
  const candidatesBundle = buildCandidates(words);

  let puzzleWords = puzzleMap.get(requestedDate);
  if (!validatePuzzleWords(puzzleWords, candidatesBundle)) {
    const seed = xmur3(requestedDate)();
    const pick = pickDailyWords(candidatesBundle, seed);
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
