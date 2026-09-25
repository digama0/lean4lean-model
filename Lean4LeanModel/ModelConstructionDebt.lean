import Lean4LeanModel.Fundamental
import Lean4Lean.Theory.Typing.Env

/-!
# Explicit declaration-model boundaries

These are the only local proof holes in the construction. The axiom theorem is retained solely for
the backwards-compatible unrestricted statement; `model_of_wfHistory_standard` bypasses it via
explicit meanings for the standard three. The inductive theorem is blocked by upstream `sorry`
definitions. The quotient mathematics and exact generated-syntax bridges are complete, while its
history step still needs the canonical equality invariant. The holes are kept in a
dedicated module so CI can reject accidental proof debt everywhere else.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- **Known-false statement placeholder.** The naive theorem permits arbitrary axioms, whose
declared types need not be inhabited: adding an axiom of `VExpr.false` is a counterexample. This is
the localized axiom case requested while the true statement admitting Lean's standard axioms is
being specified. -/
theorem model_axiom_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {ci : VConstVal}
    (M : ModelSetup κ env assignment) (hci : ci.toVConstant.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

/-- `VInductDecl.WF` and `VEnv.addInduct` are still defined by `sorry` upstream and expose no
constructor data from which to build the corresponding sets. -/
theorem model_inductive_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {decl : VInductDecl}
    (M : ModelSetup κ env assignment) (hdecl : decl.WF env)
    (hadd : env.addInduct decl = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

/-- The quotient operations, their universe closure, all four exact primitive types, and the
generated `quotDefEq` computation rule are constructed and wired into the canonical `addQuot`
model step. Applying that theorem here still requires carrying `ModelsEq` through history induction.

This theorem's present signature cannot express that induction invariant: `ModelSetup` together
with `VEnv.QuotReady` says only that `Eq` is declared, not that it has the canonical semantic
meaning recorded by `ModelsEq`. Closing the boundary therefore requires strengthening the history
induction motive (or `ModelSetup`) before proving this environment step. Since canonical `Eq`
comes from the pending inductive semantics, `addQuot` is transitively blocked on that construction
even though the quotient mathematics itself is complete. -/
theorem model_quotient_boundary {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}}
    (M : ModelSetup κ env assignment) (hready : env.QuotReady)
    (hadd : env.addQuot = some env') (henv' : env'.WF) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  sorry

end Lean4LeanModel
