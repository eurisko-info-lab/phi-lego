import Lake
open Lake DSL

package «lego» where
  version := v!"0.1.0"

lean_lib «Lego» where
  srcDir := "src"

@[default_target]
lean_exe «lego» where
  root := `Main

lean_exe «lego-test» where
  root := `Test
  -- Ensure proper linking with Init library
  moreLinkArgs := #["-lInit"]
