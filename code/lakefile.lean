import Lake
open Lake DSL

package «DMT1» where
  -- Add package configuration options here

lean_lib «DMT1» where
  -- Add library configuration options here

-- Add Mathlib dependency with a known working version
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.6.0"

@[default_target]
lean_exe «dmt1» where
  root := `Main
