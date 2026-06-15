# lean-refl-beta

**β-reduction is a refinement, not an equivalence, under reflection — in ~140 lines.**

A self-contained Lean 4 distillation of the central obstruction that lean-sage proves
for the full Black reflective tower (`beta_not_unconditional_CtxEquiv`), stripped to the
smallest calculus that still exhibits it. No dependencies beyond Lean core.

## The idea

Applying a function is performed *by the meta-level*: the evaluator at level `lvl`
reflects up to level `lvl+1` to run the apply step (in Black, `base-apply` is reified one
level up). At the top of the tower there is no level above, so application gets stuck.
The β-contractum `let x = a in b` is a core form — it binds and runs the body directly,
with no meta-level step — so it keeps running where the redex `(λx.b) a` cannot.

> You can always run the *reduced* program, but not always the *unreduced* one — because
> running an application consults the tower, and at the top there is no tower left to
> consult.

## What is proved (`ReflBeta.lean`)

All `sorry`-free; axioms ⊆ `{propext, Quot.sound}`.

| theorem | statement |
|---|---|
| `eval_app_top` | with no level above (`maxDepth ≤ lvl+1`), *every* application diverges |
| `redex_eq_contractum_of_budget` | with depth budget (`lvl+1 < maxDepth`), redex and contractum evaluate identically — **β sound** |
| `refine_forward` | redex converges ⟹ contractum converges to the same value — **forward refinement, unconditional** |
| `beta_not_ObsEq` | the Wand pair `(λx.x) 0` / `let x = 0 in x` is observationally distinguished at the top — **β not an unconditional equivalence** |
| `beta_refinement_not_equivalence` | the two halves together: refinement everywhere, equivalence only under budget |

Same witness as full Black; here the whole dividing line fits on one screen.

## Scope — what this captures, and what it doesn't

lean-refl-beta is a faithful distillation of **one** of lean-sage's obstructions — the
depth/gate one (Obstruction B, `beta_not_unconditional_CtxEquiv`) — plus the
forward/backward refinement asymmetry. Same witness, same mechanism. It is the "one
screen" version of the **headline**, not of the whole result. Nothing here contradicts
lean-sage; it is a strict sub-conclusion.

**Captured, faithfully:**
- β is a refinement, not an equivalence, because the redex's application is
  meta-level-mediated and stalls at the top of the tower (the contractum isn't).
- Forward refinement (contraction preserves convergence), unconditionally.
- Equivalence recovered exactly under depth budget.

**Not captured — see lean-sage:**
- **Obstruction A** — the *fine* (value-equality) congruence failing under `.lam`
  because closures freeze bodies, forcing ground/up-to-bisim observation
  (`lam_EvalEquiv_congruence_fails`). Here we observe *convergence* from the start,
  sidestepping A rather than exhibiting it.
- **The positive contextual congruence** — that β *is* an equivalence in the non-binder
  positions under conditions (`contextual_beta_pure`). Our positive results are
  *pointwise* (one level/env), not lifted to all contexts.
- **Actual reflection** — there is no reflective operator here (no `em`, no metacircular
  eval). We model only the *consequence* reflection imposes: application consults the
  level above. Faithful to *why* B happens, but this calculus cannot inspect its own
  evaluator.
- **Mutation / purity** — full Black has `set!`/`installPolicy` that independently break
  β (hence lean-sage's `Pure` side condition); there is none of that here.

So: this is a **model**, chosen for clarity, not a faithful formalization of Black.
lean-sage is the faithful (heavy) artifact; for the full result — all obstructions, the
positive congruence, and the open `.lam` core — see its `SUMMARY.md` and `REVERSE.md`.

## Check it

```
lake build
# or, against any Lean 4 v4.29.1 toolchain:
lake env lean ReflBeta.lean
```
