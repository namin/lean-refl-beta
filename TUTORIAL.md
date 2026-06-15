# Tutorial: why β breaks under reflection

A guided read of [`ReflBeta.lean`](./ReflBeta.lean). By the end you'll understand,
from ~140 lines of Lean, why the most basic program equation — β-reduction — *fails*
to be a contextual equivalence in a reflective language, and exactly under what
condition it survives.

No Lean expertise required to follow the prose; the snippets are short.

---

## 0. The puzzle

β-reduction is the rewrite `(λx. b) a  ↝  let x = a in b`. In an ordinary language
it's *meaning-preserving*: you can do it (or undo it) anywhere without changing what a
program does. That's what licenses inlining, and equational reasoning generally.

Mitchell Wand's "The Theory of Fexprs is Trivial" says reflection wrecks this: once a
program can inspect its own evaluation, almost no two distinct programs stay equal. The
question this artifact answers: *does β itself survive?* And if so, at what price.

The answer, in one line: **β-reduction is a refinement, not an equivalence — and the
price is depth budget.**

---

## 1. A tiny calculus (`Tm`, `Val`)

We need just enough language to write a redex and its contractum.

```lean
inductive Tm
  | lit  : Nat → Tm            -- a ground literal, e.g. `0`  (this is what we observe)
  | var  : Nat → Tm            -- de Bruijn variable
  | lam  : Tm → Tm             -- λ. body
  | app  : Tm → Tm → Tm        -- f a
  | letE : Tm → Tm → Tm        -- letE a b  =  let x = a in b
```

Values are literals and closures. A **closure** freezes a `lam`'s body together with
the environment it was created in:

```lean
inductive Val
  | lit : Nat → Val
  | clo : Tm → List Val → Val
```

That's the whole syntax. The redex and contractum are just:

```lean
def redex      (b a : Tm) : Tm := .app (.lam b) a   -- (λx. b) a
def contractum (b a : Tm) : Tm := .letE a b         -- let x = a in b
```

---

## 2. The one idea: application is done by the meta-level

This is the heart of the artifact — read the `app` and `letE` clauses of `eval`
side by side:

```lean
  | fuel+1, lvl, env, .letE a b =>
      match eval fuel lvl env a with
      | some v => eval fuel lvl (v :: env) b      -- bind a, run b. That's it.
      | none   => none
  | fuel+1, lvl, env, .app f x  =>
      match eval fuel lvl env f with
      | some (.clo b cenv) =>
          match eval fuel lvl env x with
          | some v => if lvl + 1 < maxDepth        -- ← the reflective step
                      then eval fuel lvl (v :: cenv) b
                      else none
          | none   => none
      | _ => none
```

The single reflective ingredient is the `if lvl + 1 < maxDepth` guard on `app`.

**Why is it there?** In a reflective tower, *applying* a function is not something the
evaluator does by itself — it is performed by the **meta-level**. The evaluator at level
`lvl` reflects up to level `lvl + 1` to run the apply step (in Black this is the
reified `base-apply` procedure, living one level up). So an application *consults the
level above*. At the top of the tower (`lvl + 1 ≥ maxDepth`) there is no level above,
and the application is stuck.

Crucially, `letE` does **none** of this. Binding `a` and running `b` is a core step of
the evaluator — no meta-level, no consultation, no depth requirement.

So `(λx. b) a` and `let x = a in b` differ in exactly one way: **the redex needs a level
above to fire; the contractum doesn't.**

(The `fuel` argument is just a termination counter so `eval` is a total function —
ignore it; it never affects the phenomenon.)

---

## 3. Watch it happen

Take the Wand pair: the identity applied to `0`, `(λx.x) 0`, versus `let x = 0 in x`.
Both "should" yield `0`.

**At a normal level** (say `lvl = 0`, so `0 + 1 = 1 < 8`):

- `redex`: eval `λx.x` → a closure; eval `0` → `0`; gate `1 < 8` ✓ → run the body `x`
  with `x ↦ 0` → **`0`**.
- `contractum`: bind `0`, run `x` → **`0`**.

They agree. Good.

**At the top of the tower** (`lvl = maxDepth - 1 = 7`, so `7 + 1 = 8`, *not* `< 8`):

- `redex`: eval the closure, eval `0`; gate `8 < 8` ✗ → **stuck (`none`)**. There is no
  level `8` for the apply step to reflect into.
- `contractum`: bind `0`, run `x` → **`0`**. It never needed a level above.

They **disagree**: the contractum converges where the redex cannot. That asymmetry *is*
the result.

---

## 4. The theorems

Each line of the dividing line is one short theorem. (All `sorry`-free; axioms
⊆ `{propext, Quot.sound}`.)

### 4a. The gate exhausts at the top — `eval_app_top`

```lean
theorem eval_app_top (lvl) (h : maxDepth ≤ lvl + 1) :
    ∀ fuel env, eval fuel lvl env (.app f x) = none
```

With no level above, *every* application diverges — whatever `f` and `x` are. The proof
just unfolds `eval` one step and notes the only way `app` returns a value is through the
gate, which is now `false`. This is the engine of everything below.

### 4b. β is sound *with* budget — `redex_eq_contractum_of_budget`

```lean
theorem redex_eq_contractum_of_budget (h : lvl + 1 < maxDepth) (b a) (fuel) (env) :
    eval fuel lvl env (redex b a) = eval fuel lvl env (contractum b a)
```

When the gate *can* fire, the redex and contractum evaluate **identically** — both bind
`a`'s value and run `b`. (The closure's captured environment is exactly the ambient one,
so "run `b` with `x ↦ a`" means the same thing on both sides.) Proof: unfold both, the
`if` is `true` by `h`, the two sides become the same expression.

### 4c. The forward direction is free — `refine_forward`

```lean
theorem refine_forward (hr : eval fuel lvl env (redex b a) = some r) :
    eval fuel lvl env (contractum b a) = some r
```

If the *redex* converges, so does the contractum, to the same value — **with no budget
hypothesis**. Why is it free? Because if the redex converged, the gate *must* have fired
(`eval_app_top` says otherwise it would be `none`), so the budget held after all —
*convergence of the redex supplies its own budget.* Then 4b finishes the job.

This is the precise sense in which **β-contraction preserves convergence**: doing the
reduction never breaks a program that was already running.

### 4d. ...but not the backward direction — `beta_not_ObsEq` (the gem)

```lean
theorem beta_not_ObsEq :
    ¬ ObsEq (redex (.var 0) (.lit 0)) (contractum (.var 0) (.lit 0))
```

where `ObsEq t1 t2` means "`t1` and `t2` converge in exactly the same situations."
The proof is the trace from §3: at `lvl = 7` the contractum converges (`⟨3, .lit 0, …⟩`)
but the redex is `none` for *every* fuel (`eval_app_top`). One witness, and the
equivalence is refuted.

This is the model's form of lean-sage's `beta_not_unconditional_CtxEquiv` — the same
Wand pair, distinguished for the same reason: the redex's apply has no level to reflect
into at the top of the tower.

So you cannot freely *un-reduce* (β-expand): replacing `let x = a in b` by `(λx.b) a`
can turn a working program into a stuck one.

### 4e. Both halves together — `beta_refinement_not_equivalence`

```lean
theorem beta_refinement_not_equivalence :
    (∀ b a lvl env, Converges lvl env (redex b a) → Converges lvl env (contractum b a))
    ∧ (¬ ObsEq (redex (.var 0) (.lit 0)) (contractum (.var 0) (.lit 0)))
```

Refinement everywhere (left), equivalence-failure (right). Combined with 4b: the two are
*equivalent* exactly when the application has depth budget.

---

## 5. The takeaway

> Under reflection you can always run the **reduced** program, but not always the
> **unreduced** one — because running an application consults the tower, and at the top
> there is no tower left to consult.

That's the whole story: β is **convergence-preserving but not convergence-reflecting**.
The contractum is strictly more defined than the redex; they coincide only under a depth
budget, which is provably necessary (`beta_not_ObsEq`).

## 6. Try it yourself

- Change `def maxDepth : Nat := 8` to `2` and re-`lake build`. The phenomenon is the
  same; only the cliff moves.
- Replace the body `.var 0` with `.lit 5` in `beta_not_ObsEq` and adjust — the redex
  still diverges at the top, the contractum still converges. The identity isn't special;
  *application* is.
- Try to prove `ObsEq (redex (.var 0) (.lit 0)) (contractum (.var 0) (.lit 0))`. You
  can't — and §4d shows exactly where you'd get stuck (`lvl = 7`).

## 7. Where this comes from

This is a deliberately small **model** of the obstruction. The faithful formalization,
for the actual Black reflective tower, is **lean-sage** — there the same fact is
`beta_not_unconditional_CtxEquiv`, the apply genuinely materializes `level+1`, and the
full dividing line (with the open `.lam` congruence) lives in its `SUMMARY.md` and
`REVERSE.md`. Read this file to understand the idea; read lean-sage to see it done for
real.
