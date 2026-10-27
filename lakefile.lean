import Lake
open Lake DSL

package cairn where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

/-- fdatasync / F_FULLFSYNC and directory fsync. Linked into every executable. -/
extern_lib cairn_sync pkg := do
  let srcJob ← inputTextFile <| pkg.dir / "native" / "cairn_sync.c"
  let oFile := pkg.buildDir / "native" / "cairn_sync.o"
  let includeDir ← getLeanIncludeDir
  let oJob ← buildO oFile srcJob #["-fPIC", "-I", includeDir.toString] #[]
  -- `NPackage` has `staticLibDir` (`buildDir` / `lib`). The linker uses this path.
  buildStaticLib (pkg.staticLibDir / nameToStaticLib "cairn_sync") #[oJob]

@[default_target]
lean_lib Cairn

@[test_driver]
lean_exe «cairn-tests» where
  root := `Tests.Main

lean_exe «cairn-bench» where
  root := `Bench.Main

lean_exe «cairn-durable-bench» where
  root := `Bench.Durable

lean_exe «cairn-design-bench» where
  root := `Bench.Design

lean_exe «cairn-sync-trace» where
  root := `Demo.SyncTrace

lean_exe «cairn-crash-writer» where
  root := `Demo.Writer

lean_exe «cairn-recover» where
  root := `Demo.Recover
