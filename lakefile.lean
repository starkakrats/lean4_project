import Lake
open Lake DSL

package «my_project» {
  moreLinkArgs := #["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MyProject» {
  -- add any library configuration options here
}

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.2"

require Duper from git "https://github.com/leanprover-community/duper.git" @ "v0.0.5"

require aesop from git "https://github.com/JLimperg/aesop"
