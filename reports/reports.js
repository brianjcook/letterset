const REPORT_ENDPOINT = '../session.php';

const tbody = document.getElementById('sessions');
const summaryEl = document.getElementById('summary');
const statusEl = document.getElementById('status');
const refreshBtn = document.getElementById('refresh');

function formatDate(value) {
  if (!value) return '';
  const date = new Date(value);
  if (Number.isNaN(date.getTime())) return value;
  return date.toLocaleString();
}

function formatDuration(seconds) {
  if (seconds === null || seconds === undefined || seconds === '') return '';
  const total = Math.max(0, Number(seconds));
  if (!Number.isFinite(total)) return '';
  const h = Math.floor(total / 3600);
  const m = Math.floor((total % 3600) / 60);
  const s = Math.floor(total % 60);
  const parts = [];
  if (h) parts.push(`${h}h`);
  if (m) parts.push(`${m}m`);
  if (s || !parts.length) parts.push(`${s}s`);
  return parts.join(' ');
}

function shortId(id) {
  if (!id) return '';
  if (id.length <= 18) return id;
  return `${id.slice(0, 8)}...${id.slice(-6)}`;
}

function renderRows(rows) {
  tbody.innerHTML = '';
  if (!rows.length) {
    const tr = document.createElement('tr');
    const td = document.createElement('td');
    td.colSpan = 6;
    td.textContent = 'No sessions recorded yet.';
    tr.appendChild(td);
    tbody.appendChild(tr);
    return;
  }

  for (const row of rows) {
    const tr = document.createElement('tr');
    const cells = [
      { value: shortId(row.session_id), className: 'mono', title: row.session_id },
      { value: row.game_id || '', className: 'mono' },
      { value: formatDate(row.session_start) },
      { value: String(row.submit_attempts || 0) },
      { value: row.solved ? formatDuration(row.time_to_solve_seconds) : '' },
      { value: row.solution_set || '', className: 'mono' }
    ];

    for (const cell of cells) {
      const td = document.createElement('td');
      td.textContent = cell.value;
      if (cell.className) td.className = cell.className;
      if (cell.title) td.title = cell.title;
      tr.appendChild(td);
    }
    tbody.appendChild(tr);
  }
}

async function loadReports() {
  statusEl.textContent = '';
  refreshBtn.disabled = true;
  try {
    const response = await fetch(REPORT_ENDPOINT, { cache: 'no-store' });
    if (!response.ok) throw new Error(`Request failed (${response.status})`);
    const data = await response.json();
    const sessions = Array.isArray(data.sessions) ? data.sessions : [];
    renderRows(sessions);
    summaryEl.textContent = `${sessions.length} sessions recorded`;
  } catch (err) {
    statusEl.textContent = `Unable to load reports: ${err.message}`;
  } finally {
    refreshBtn.disabled = false;
  }
}

refreshBtn.addEventListener('click', loadReports);
loadReports();
