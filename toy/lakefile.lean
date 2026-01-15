import Lake
open Lake DSL

package «lego» where
  version := v!"0.1.0"

lean_lib «Lego» where
  srcDir := "src"

-- Generated code (from ToLean)
lean_lib «LegoGenerated» where
  srcDir := "generated"
  roots := #[`BootstrapGrammar, `BootstrapTokenizer, `BootstrapRules]

@[default_target]
lean_exe «lego» where
  root := `Main

lean_exe «lego-test» where
  root := `Test
  -- Ensure proper linking with Init library
  moreLinkArgs := #["-lInit"]

-- Tools
lean_exe «toantlr» where
  root := `tools.ToAntlr

lean_exe «totreesitter» where
  root := `tools.ToTreeSitter

lean_exe «tolean» where
  root := `tools.ToLean
