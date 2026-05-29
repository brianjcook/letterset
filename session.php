<?php
declare(strict_types=1);

header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store');

$dataDir = __DIR__ . '/_report_data';
$logFile = $dataDir . '/session-events.jsonl';

function send_json(array $payload, int $status = 200): void
{
    http_response_code($status);
    echo json_encode($payload, JSON_UNESCAPED_SLASHES);
    exit;
}

function clean_text($value, int $maxLength = 200): string
{
    $value = is_string($value) ? $value : '';
    $value = preg_replace('/[^\P{C}\t]/u', '', $value) ?? '';
    return substr(trim($value), 0, $maxLength);
}

function clean_int($value): ?int
{
    if ($value === null || $value === '') return null;
    if (!is_numeric($value)) return null;
    return max(0, (int) $value);
}

function ensure_data_dir(string $dataDir): void
{
    if (is_dir($dataDir)) return;
    if (!mkdir($dataDir, 0755, true) && !is_dir($dataDir)) {
        send_json(['ok' => false, 'error' => 'Unable to create report data directory.'], 500);
    }
}

function read_sessions(string $logFile): array
{
    if (!is_file($logFile)) return [];

    $sessions = [];
    $handle = fopen($logFile, 'r');
    if (!$handle) return [];

    while (($line = fgets($handle)) !== false) {
        $event = json_decode($line, true);
        if (!is_array($event) || empty($event['session_id'])) continue;

        $sessionId = (string) $event['session_id'];
        if (!isset($sessions[$sessionId])) {
            $sessions[$sessionId] = [
                'session_id' => $sessionId,
                'game_id' => '',
                'session_start' => '',
                'submit_attempts' => 0,
                'time_to_solve_seconds' => null,
                'solution_set' => '',
                'solved' => false
            ];
        }

        $row = &$sessions[$sessionId];
        if (!empty($event['game_id'])) $row['game_id'] = (string) $event['game_id'];
        if (!empty($event['session_start'])) $row['session_start'] = (string) $event['session_start'];
        if (!empty($event['solution_set'])) $row['solution_set'] = (string) $event['solution_set'];
        if (($event['event'] ?? '') === 'submit_attempt') $row['submit_attempts']++;

        if (($event['event'] ?? '') === 'submit_success') {
            $row['solved'] = true;
            $time = clean_int($event['time_to_solve_seconds'] ?? $event['elapsed_seconds'] ?? null);
            if ($time !== null) $row['time_to_solve_seconds'] = $time;
        }
        unset($row);
    }

    fclose($handle);
    $rows = array_values($sessions);
    usort($rows, function (array $a, array $b): int {
        return strcmp((string) $b['session_start'], (string) $a['session_start']);
    });

    return $rows;
}

if ($_SERVER['REQUEST_METHOD'] === 'GET') {
    send_json(['ok' => true, 'sessions' => read_sessions($logFile)]);
}

if ($_SERVER['REQUEST_METHOD'] !== 'POST') {
    send_json(['ok' => false, 'error' => 'Method not allowed.'], 405);
}

$raw = file_get_contents('php://input');
$payload = json_decode($raw ?: '', true);
if (!is_array($payload)) {
    send_json(['ok' => false, 'error' => 'Invalid JSON.'], 400);
}

$sessionId = clean_text($payload['session_id'] ?? '', 80);
if (!preg_match('/^[A-Za-z0-9_-]{8,80}$/', $sessionId)) {
    send_json(['ok' => false, 'error' => 'Invalid session ID.'], 400);
}

$event = [
    'event' => clean_text($payload['event'] ?? '', 60),
    'session_id' => $sessionId,
    'game_id' => clean_text($payload['game_id'] ?? '', 80),
    'session_start' => clean_text($payload['session_start'] ?? '', 40),
    'timestamp' => clean_text($payload['timestamp'] ?? '', 40),
    'server_received_at' => gmdate('c'),
    'solution_set' => clean_text($payload['solution_set'] ?? '', 40),
    'submit_attempts' => clean_int($payload['submit_attempts'] ?? $payload['attempt_count'] ?? null),
    'time_to_solve_seconds' => clean_int($payload['time_to_solve_seconds'] ?? $payload['elapsed_seconds'] ?? null)
];

ensure_data_dir($dataDir);
$line = json_encode($event, JSON_UNESCAPED_SLASHES) . PHP_EOL;
$written = file_put_contents($logFile, $line, FILE_APPEND | LOCK_EX);
if ($written === false) {
    send_json(['ok' => false, 'error' => 'Unable to write report event.'], 500);
}

send_json(['ok' => true]);
