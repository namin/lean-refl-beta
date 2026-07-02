/-
  Audit.lean — machine-pinned axiom footprints for the headline theorems.

  The README's claim "axioms ⊆ {propext, Quot.sound}; no sorry, no native_decide"
  is witnessed here, not just asserted: each `#guard_msgs in #print axioms` fails
  the build if a theorem's footprint changes (a stray `native_decide` would inject
  `Lean.ofReduceBool`; a `sorry` would inject `sorryAx`).
-/
import ReflBeta

/-- info: 'ReflBeta.eval_app_top' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReflBeta.eval_app_top

/-- info: 'ReflBeta.redex_eq_contractum_of_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReflBeta.redex_eq_contractum_of_budget

/-- info: 'ReflBeta.refine_forward' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReflBeta.refine_forward

/-- info: 'ReflBeta.beta_refines' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReflBeta.beta_refines

/-- info: 'ReflBeta.beta_not_ObsEq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReflBeta.beta_not_ObsEq

/-- info: 'ReflBeta.beta_refinement_not_equivalence' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ReflBeta.beta_refinement_not_equivalence
