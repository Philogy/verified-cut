import Lake

open Lake DSL

require «verso-slides» from git "https://github.com/leanprover/verso-slides.git"@"v4.36.0-rc1"

package «verified-cut-slides» where
  version := v!"0.1.0"

lean_lib Talk

@[default_target] lean_exe slides where root := `Main
