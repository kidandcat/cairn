/-
Byte storage. The core never sees a file descriptor.

`append` and `replaceAll` are the only writers. `sync` pushes buffered writes as far
as the backend can: the memory backend is a no-op, the file backend calls
`Handle.flush`. Lean 4.35 has no `fsync`, so a flushed file survives `kill -9`
(the kernel page cache) and is not a power-loss barrier.

Compaction writes a temp file, flushes it, drops that handle, then `rename`s it
over the live path. The append handle is cleared before the rename so it does
not keep the old inode.
-/

import Cairn.Bytes
import Cairn.Record

open System

namespace Cairn

structure Store where
  readAll : IO Bytes
  append : Bytes → IO Unit
  sync : IO Unit
  replaceAll : Bytes → IO Unit

def Store.mem (buf : IO.Ref Bytes) : Store where
  readAll := buf.get
  append b := buf.modify (· ++ b)
  sync := pure ()
  replaceAll := buf.set

/-- Write `bytes` to a temp file and rename it onto `path`. The temp handle does not escape. -/
def writeAside (path : FilePath) (bytes : Bytes) : IO Unit := do
  let tmp := FilePath.mk (path.toString ++ ".cairn-tmp")
  let h ← IO.FS.Handle.mk tmp .write
  h.write bytes.toByteArray
  h.flush
  IO.FS.rename tmp path

def Store.file (path : FilePath) (handle : IO.Ref (Option IO.FS.Handle)) : Store where
  readAll := do
    return (← IO.FS.readBinFile path).toList
  append b := do
    match ← handle.get with
    | some h => h.write b.toByteArray
    | none => throw (IO.userError "store has no append handle")
  sync := do
    match ← handle.get with
    | some h => h.flush
    | none => pure ()
  replaceAll b := do
    handle.set none
    writeAside path b
    let h ← IO.FS.Handle.mk path .append
    handle.set (some h)

def Store.openFile (path : FilePath) : IO Store := do
  if !(← path.pathExists) then
    let h ← IO.FS.Handle.mk path .write
    h.write (encodeFile []).toByteArray
    h.flush
  let handle ← IO.mkRef (some (← IO.FS.Handle.mk path .append))
  return Store.file path handle

end Cairn
