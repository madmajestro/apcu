--TEST--
Disable hugepage
--SKIPIF--
<?php
require_once(dirname(__FILE__) . '/skipif.inc'); 

// is mmap used?
if (ini_get('apc.mmap_hugepage_size') === false) die("skip mmap is not used");
?>
--INI--
apc.enabled=1
apc.enable_cli=1
apc.mmap_hugepage_size=0
apc.shm_size=2M
--FILE--
===DONE===
--EXPECT--
===DONE===
