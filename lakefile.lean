import Lake
open Lake DSL

package cairn where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

@[default_target]
lean_lib Cairn

@[test_driver]
lean_exe «cairn-tests» where
  root := `Tests.Main

lean_exe «cairn-bench» where
  root := `Bench.Main

lean_exe «cairn-crash-writer» where
  root := `Demo.Writer

lean_exe «cairn-recover» where
  root := `Demo.Recover
