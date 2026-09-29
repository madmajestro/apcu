--TEST--
APCUIterator: not serializable
--SKIPIF--
<?php
require_once(dirname(__FILE__) . '/skipif.inc');
if (PHP_VERSION_ID < 80100) die('skip PHP 8.1+ only');
?>
--INI--
apc.enabled=1
apc.enable_cli=1
--FILE--
<?php
try {
    serialize(new APCUIterator());
} catch (Exception $e) {
    echo $e->getMessage(), "\n";
}
try {
    unserialize('O:12:"APCUIterator":0:{}');
} catch (Exception $e) {
    echo $e->getMessage(), "\n";
}
?>
--EXPECT--
Serialization of 'APCUIterator' is not allowed
Unserialization of 'APCUIterator' is not allowed
