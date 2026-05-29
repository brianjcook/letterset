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
- Added a temporary `php-test.php` endpoint to verify whether PHP executes under the Letterset deployment path.
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
- `php-test.php`: temporary PHP execution diagnostic endpoint.
- `_report_data/.htaccess`: denies direct browser access to report storage.
- `.github/workflows/deploy.yml`: FTP deployment workflow.

## Deployment/runtime status
- GitHub Actions deploys from `master` to Freehostia FTP `server-dir: /letterset/`.
- Local validation passed for the reporting endpoint:
  - `php -l session.php`
  - `php -l php-test.php`
  - `node --check app.js`
  - `node --check reports/reports.js`
  - Local PHP built-in-server GET/POST smoke test against `php-test.php` and `session.php`.
- Live PHP execution under `/games/letterset/` is still being verified. Earlier live requests to PHP returned 403 or Drupal-style 400 responses before `session.php` was made self-contained.

## Recent commits
- `894156a` Bust cached Letterset scripts
- `5b450d0` Deploy Letterset to live FTP path
- `f469b68` Add local reports fallback
- `8a5062e` Allow Letterset PHP endpoint
- `bb4ee30` Move report endpoint to root

## Next priority tasks
- Deploy and test `https://thecookblog.com/games/letterset/php-test.php`.
- Deploy and test `https://thecookblog.com/games/letterset/session.php` with GET and POST.
- If PHP still fails under `/games/letterset/`, ask the user to either adjust permissions or place the endpoint in the actual PHP-executing site root, then update `SESSION_REPORT_PATH` and `REPORT_ENDPOINT`.
- Remove `php-test.php` after PHP execution is confirmed or after an alternate endpoint path is chosen.

## Resume prompt for a brand-new Codex session
Read `CODEX_CONTEXT.md`, inspect `git status`, then continue verifying the Letterset reports endpoint. If `php-test.php` and `session.php` have not been deployed yet, commit and push the current reporting endpoint changes, wait for GitHub Actions to finish, then test the live PHP endpoints under `https://thecookblog.com/games/letterset/`. If live PHP still returns 403 or Drupal-style 400 responses, coordinate with the user on CHMOD or moving the endpoint to the actual root folder and update the JS endpoint URLs accordingly.
