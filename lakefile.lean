import Lake
open Lake DSL

package «lean-refl-beta» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib «ReflBeta» where
  srcDir := "."
