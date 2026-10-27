/-
Native durability syscalls. This is the only module that calls C.

`datasync` is `fdatasync` on Linux and `F_FULLFSYNC` (falling back to
`fsync`) on macOS. `syncDir` fsyncs the parent directory so a create or
rename is durable. The codec, the map, and the crash theorems do not
import this module.
-/

namespace Cairn.Posix

@[extern "cairn_open_append"]
opaque openAppend (path : @& String) : IO UInt32

@[extern "cairn_open_trunc"]
opaque openTrunc (path : @& String) : IO UInt32

@[extern "cairn_write"]
opaque write (fd : UInt32) (buf : @& ByteArray) : IO Unit

@[extern "cairn_datasync"]
opaque datasync (fd : UInt32) : IO Unit

@[extern "cairn_close_fd"]
opaque closeFd (fd : UInt32) : IO Unit

@[extern "cairn_sync_dir"]
opaque syncDir (path : @& String) : IO Unit

end Cairn.Posix
