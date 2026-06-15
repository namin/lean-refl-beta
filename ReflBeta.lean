/-
  lean-refl-beta — β is a *refinement*, not an *equivalence*, under reflection.

  The phenomenon of lean-sage's `beta_not_unconditional_CtxEquiv`, distilled to the
  smallest calculus that still exhibits it. No imports beyond Lean core.

  ## The idea

  In a reflective tower, *applying* a function is performed by the meta-level: the
  evaluator at level `lvl` reflects up to level `lvl+1` to run the apply step (in Black,
  `base-apply` is reified one level up). At the top of the tower there is no level
  above, so application gets stuck. The β-contractum `let x = a in b` is a core form —
  it binds `a` and runs `b` directly, with no meta-level step — so it keeps running
  where the redex `(λx.b) a` cannot.

  Hence β-contraction is **convergence-preserving but not convergence-reflecting**: the
  contractum is *more defined* than the redex. They coincide only when the application
  has depth budget. Same witness as full Black: `(λx.x) 0` vs `let x = 0 in x`.

  Check with:  lake env lean ReflBeta.lean   (from a Lean 4 toolchain)
-/

namespace ReflBeta

/-- Tower height. An application consults the level above, which must be `< maxDepth`. -/
def maxDepth : Nat := 8

/-- A tiny λ-calculus with `let`, over de Bruijn indices, plus ground literals. -/
inductive Tm where
  | lit  : Nat → Tm
  | var  : Nat → Tm
  | lam  : Tm → Tm
  | app  : Tm → Tm → Tm
  | letE : Tm → Tm → Tm            -- `letE a b`  =  `let x = a in b`
  deriving Repr

/-- Values: ground literals and closures (a *frozen* body + captured environment). -/
inductive Val where
  | lit : Nat → Val
  | clo : Tm → List Val → Val
  deriving Repr

abbrev Env := List Val

/-- Level-indexed evaluator. The **only** reflective ingredient is the `app` clause:
    the apply step is run by the meta-level, so it needs a level above
    (`lvl + 1 < maxDepth`). Every other form — crucially `letE`, the β-contractum — is
    handled directly and needs no level above. -/
def eval : Nat → Nat → Env → Tm → Option Val
  | 0,      _,   _,   _         => none
  | _+1,    _,   _,   .lit k    => some (.lit k)
  | _+1,    _,   env, .var i    => env[i]?
  | _+1,    _,   env, .lam b    => some (.clo b env)
  | fuel+1, lvl, env, .letE a b =>
      match eval fuel lvl env a with
      | some v => eval fuel lvl (v :: env) b
      | none   => none
  | fuel+1, lvl, env, .app f x  =>
      match eval fuel lvl env f with
      | some (.clo b cenv) =>
          match eval fuel lvl env x with
          | some v => if lvl + 1 < maxDepth then eval fuel lvl (v :: cenv) b else none
          | none   => none
      | _ => none

/-- The β-redex `(λx.b) a` and its contractum `let x = a in b`. -/
def redex      (b a : Tm) : Tm := .app (.lam b) a
def contractum (b a : Tm) : Tm := .letE a b

/-! ## The reflective obstruction -/

/-- **Application exhausts at the top of the tower.** With no level above
    (`maxDepth ≤ lvl + 1`) the apply step has nowhere to reflect into, so *every*
    application diverges — whatever the function and argument are. -/
theorem eval_app_top (lvl : Nat) {f x : Tm} (h : maxDepth ≤ lvl + 1) :
    ∀ (fuel : Nat) (env : Env), eval fuel lvl env (.app f x) = none := by
  intro fuel env
  cases fuel with
  | zero => rfl
  | succ k =>
      simp only [eval]
      cases hf : eval k lvl env f with
      | none => rfl
      | some v =>
          cases v with
          | lit _ => rfl
          | clo b cenv =>
              cases hx : eval k lvl env x with
              | none => rfl
              | some w => exact if_neg (by omega)

/-- **β is sound under budget.** When the application can reflect
    (`lvl + 1 < maxDepth`), the redex and the contractum evaluate identically: both
    bind `a`'s value and run `b`. -/
theorem redex_eq_contractum_of_budget {lvl : Nat} (h : lvl + 1 < maxDepth) (b a : Tm)
    (fuel : Nat) (env : Env) :
    eval fuel lvl env (redex b a) = eval fuel lvl env (contractum b a) := by
  cases fuel with
  | zero => simp [eval]
  | succ f =>
      cases f with
      | zero => simp [redex, contractum, eval]
      | succ k => simp [redex, contractum, eval, h]

/-- **β-contraction preserves convergence (forward refinement).** If the redex
    converges, the gate must have fired, so the contractum converges to the *same*
    value — unconditionally (convergence itself supplies the budget). -/
theorem refine_forward {b a : Tm} {r : Val} {lvl fuel : Nat} {env : Env}
    (hr : eval fuel lvl env (redex b a) = some r) :
    eval fuel lvl env (contractum b a) = some r := by
  have hbudget : lvl + 1 < maxDepth := by
    by_cases hb : lvl + 1 < maxDepth
    · exact hb
    · exfalso
      have hge : maxDepth ≤ lvl + 1 := by omega
      simp only [redex] at hr
      rw [eval_app_top lvl hge fuel env] at hr
      exact absurd hr (by simp)
  rw [← redex_eq_contractum_of_budget hbudget b a fuel env]
  exact hr

/-! ## The dividing line -/

/-- A term *converges* (at a level, in an environment) if some fuel yields a value. -/
def Converges (lvl : Nat) (env : Env) (t : Tm) : Prop :=
  ∃ (fuel : Nat) (v : Val), eval fuel lvl env t = some v

/-- Observational equivalence: same convergence behaviour at every level and env.
    (Pointwise already refutes a contextual equivalence — the empty context is a
    context — which is all the negative result below needs.) -/
def ObsEq (t1 t2 : Tm) : Prop :=
  ∀ (lvl : Nat) (env : Env), Converges lvl env t1 ↔ Converges lvl env t2

/-- Forward: contraction never loses convergence. -/
theorem beta_refines {b a : Tm} {lvl : Nat} {env : Env}
    (h : Converges lvl env (redex b a)) : Converges lvl env (contractum b a) := by
  obtain ⟨fuel, r, hr⟩ := h
  exact ⟨fuel, r, refine_forward hr⟩

/-- **The gem: β is not an unconditional equivalence.** The Wand pair `(λx.x) 0` and
    `let x = 0 in x` are observationally distinguished — at the top of the tower
    (`lvl = maxDepth - 1`) the contractum converges to `0` while the redex's apply has
    no level to reflect into and diverges. -/
theorem beta_not_ObsEq :
    ¬ ObsEq (redex (.var 0) (.lit 0)) (contractum (.var 0) (.lit 0)) := by
  intro h
  have hcon : Converges 7 [] (contractum (.var 0) (.lit 0)) :=
    ⟨3, .lit 0, by simp [contractum, eval]⟩
  obtain ⟨fuel, v, hv⟩ := (h 7 []).mpr hcon
  simp only [redex] at hv
  rw [eval_app_top 7 (by decide) fuel []] at hv
  exact absurd hv (by simp)

/-- **β is a refinement, not an equivalence, under reflection.** Forward: contraction
    preserves convergence everywhere (`beta_refines`). Not backward: the contractum
    converges where the redex cannot (`beta_not_ObsEq`). Equivalence is recovered
    exactly under depth budget (`redex_eq_contractum_of_budget`). -/
theorem beta_refinement_not_equivalence :
    (∀ (b a : Tm) (lvl : Nat) (env : Env),
        Converges lvl env (redex b a) → Converges lvl env (contractum b a))
    ∧ (¬ ObsEq (redex (.var 0) (.lit 0)) (contractum (.var 0) (.lit 0))) :=
  ⟨fun _ _ _ _ => beta_refines, beta_not_ObsEq⟩

end ReflBeta
