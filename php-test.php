<?php
header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store');

$dataDir = __DIR__ . '/_report_data';
$writeOk = false;

if ((is_dir($dataDir) || mkdir($dataDir, 0755, true)) && is_writable($dataDir)) {
    $testFile = $dataDir . '/.write-test-' . bin2hex(random_bytes(4));
    $writeOk = file_put_contents($testFile, 'ok', LOCK_EX) !== false;
    if (is_file($testFile)) {
        unlink($testFile);
    }
}

echo json_encode([
    'ok' => true,
    'endpoint' => 'letterset-php-test',
    'report_data_writable' => $writeOk
], JSON_UNESCAPED_SLASHES);
