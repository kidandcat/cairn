/-
Byte storage. The core never sees a file descriptor.

`sync` contract. After `sync` returns, every `append` and `replaceAll` since the
previous successful `sync` survives a power loss. Bytes not covered by a
completed `sync` may be absent, reordered, or torn on a `blockSize` boundary,
including a sector that keeps only a prefix of its new contents. The caller
acknowledges a commit only after `sync` returns.

The memory backend's `sync` is not a disk: it returns immediately and the
bytes are only in the `IO.Ref`. The file backend's `sync` is `fdatasync` on
Linux and `F_FULLFSYNC` (falling back to `fsync`) on macOS. `replaceAll`
writes a new file, data-syncs it, renames it onto the target, and fsyncs the
parent directory before it returns. A crash before the rename leaves the
previous file. A crash after the rename but before the directory fsync can
show either name; both files were data-synced, so either image is a complete
cairn file.
-/

import Cairn.Bytes
import Cairn.FileFmt
import Cairn.Posix

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

/-- Data-sync `bytes` into a temp file, rename it onto `path`, fsync the directory. -/
def writeDurable (path : FilePath) (bytes : Bytes) : IO Unit := do
  let tmp := path.toString ++ ".cairn-tmp"
  let fd ← Posix.openTrunc tmp
  Posix.write fd bytes.toByteArray
  Posix.datasync fd
  Posix.closeFd fd
  IO.FS.rename tmp path
  Posix.syncDir path.toString

def Store.file (path : FilePath) (fdRef : IO.Ref (Option UInt32)) : Store where
  readAll := do
    return (← IO.FS.readBinFile path).toList
  append b := do
    match ← fdRef.get with
    | some fd => Posix.write fd b.toByteArray
    | none => throw (IO.userError "store has no append handle")
  sync := do
    match ← fdRef.get with
    | some fd => Posix.datasync fd
    | none => pure ()
  replaceAll b := do
    match ← fdRef.get with
    | some fd =>
        Posix.closeFd fd
        fdRef.set none
    | none => pure ()
    writeDurable path b
    let fd ← Posix.openAppend path.toString
    fdRef.set (some fd)

def Store.openFile (path : FilePath) : IO Store := do
  if !(← path.pathExists) then
    let fd ← Posix.openTrunc path.toString
    Posix.write fd encodeHeader.toByteArray
    Posix.datasync fd
    Posix.closeFd fd
    Posix.syncDir path.toString
  let fd ← Posix.openAppend path.toString
  let fdRef ← IO.mkRef (some fd)
  return Store.file path fdRef

/--
Rewrite a torn or mid-log-corrupt file down to the scanned prefix, durably.
A foreign file (`.reject`) is left untouched and reported. A clean file is
not rewritten.
-/
def Store.repairFile (path : FilePath) : IO Unit := do
  if !(← path.pathExists) then
    return
  let bytes := (← IO.FS.readBinFile path).toList
  let s := scan bytes
  match s.kind with
  | .reject => throw (IO.userError "not a cairn file")
  | .clean => pure ()
  | .torn | .corrupt =>
      let kept := if s.consumed = 0 then encodeHeader else bytes.take s.consumed
      if bytes != kept then
        writeDurable path kept

end Cairn
