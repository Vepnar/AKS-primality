import Lake
open Lake DSL

package «lean_tutorial» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib" @ "git#stable"

@[default_target]
lean_lib «LeanTutorial» where
  -- add any library configuration options here
