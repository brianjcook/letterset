# Letterset Codex Context

## Purpose
Letterset is a daily five-letter word puzzle at `/games/letterset/`. Players use each of 15 letters once to make three valid five-letter words.

## Current scope and decisions
- The app is static HTML/CSS/JS with lightweight PHP endpoints for reporting.
- Deployments run through GitHub Actions over FTP to Freehostia.
- The live app path is expected to be `https://thecookblog.com/games/letterset/`.
- Reports are intended to be available at `/games/letterset/reports/`.
- Reporting should not collect IP addresses.
- Session rows should include session ID, game ID, session start datetime, submit attempt count, time to solve, and solution letter set formatted as `XXXXX / YYYYY / ZZZZZ`.
- Client-side `localStorage` remains as a fallback if the PHP reporting endpoint is unavailable.

## Implemented work summary
- Added GA4/client events for game load, puzzle start, submit attempts, success/failure, and reset.
- Added `reports/` static dashboard that reads aggregated sessions from `session.php` and falls back to local browser data.
- Added root-level `session.php` as the reporting endpoint. It stores newline-delimited JSON events in `_report_data/session-events.jsonl` and aggregates them for the dashboard.
- Added `_report_data/.htaccess` to deny direct public access to stored report data.
- Temporarily deployed `php-test.php` to verify PHP execution and report-data writability, then removed it after confirmation.
- Added `.gitignore` entries for local source wordlist scratch files and generated report data.
- Updated the deploy workflow to exclude `CODEX_CONTEXT.md` from FTP deployment.

## Key files/entry points
- `index.html`: main game page.
- `app.js`: game logic, GA4 events, and session reporting client.
- `styles.css`: main game styles.
- `puzzles.json`: generated daily puzzle schedule.
- `solutions/`: solutions page.
- `reports/index.html`: reports dashboard shell.
- `reports/reports.js`: reports dashboard data loading/rendering.
- `session.php`: server-side reporting endpoint.
- `_report_data/.htaccess`: denies direct browser access to report storage.
- `.github/workflows/deploy.yml`: FTP deployment workflow.

## Deployment/runtime status
- GitHub Actions deploys from `master` to Freehostia FTP `server-dir: /letterset/`.
- Local validation passed for the reporting endpoint:
  - `php -l session.php`
  - `node --check app.js`
  - `node --check reports/reports.js`
  - Local PHP built-in-server GET/POST smoke test against `session.php`.
- Live PHP execution under `/games/letterset/` is confirmed.
- `https://thecookblog.com/games/letterset/php-test.php` returned 200 while deployed and confirmed `_report_data` was writable.
- `https://thecookblog.com/games/letterset/session.php` returned 200 JSON with `{"ok":true,"sessions":[]}` before any live sessions were recorded.
- A live invalid POST to `session.php` returned the expected 400 JSON validation response, confirming POST requests reach the endpoint without being intercepted.
- `https://thecookblog.com/games/letterset/reports/` returned 200 HTML.
- `php-test.php` has been removed from the repo and live server; the live URL now returns 404.

## Recent commits
- `894156a` Bust cached Letterset scripts
- `0478ebd` Add root Letterset report endpoint diagnostic
- `8ef2986` Check Letterset report data writability
- `681807e` Remove Letterset PHP diagnostic
- `5b450d0` Deploy Letterset to live FTP path
- `f469b68` Add local reports fallback
- `8a5062e` Allow Letterset PHP endpoint

## Next priority tasks
- Let real gameplay create the first server-side report rows.
- If `reports/` still shows the local fallback after a real play session, inspect browser network requests to `session.php` and confirm POST status.
- Consider adding lightweight access protection for `reports/` if the dashboard should not be publicly viewable.

## Resume prompt for a brand-new Codex session
Read `CODEX_CONTEXT.md`, inspect `git status`, and continue Letterset work from the current reports implementation. Live PHP under `/games/letterset/` has been confirmed. The next check is to play or simulate a real session and confirm `session.php` receives POST events and `reports/` shows server-side rows instead of local fallback data.
