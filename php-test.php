<?php
header('Content-Type: application/json; charset=utf-8');
header('Cache-Control: no-store');
echo json_encode([
    'ok' => true,
    'endpoint' => 'letterset-php-test'
], JSON_UNESCAPED_SLASHES);
