import Lean4LeanModel.AxiomEnv
import Lean4Lean.Theory.Typing.Lemmas
import Mathlib.SetTheory.Cardinal.Regular

/-!
# Consistency

What it means for an environment to be consistent, and why consistency has to be stated relative
to a base environment of axioms.

The theorems themselves are in `Lean4LeanModel.Model`, which gets them from a model.
-/

namespace Lean4LeanModel

open Lean4Lean Cardinal

universe u

/--
`∀ (α : Sort 0), α`, i.e. `∀ (p : Prop), p`.

This is the environment-independent stand-in for `False`: a `VEnv` need not contain the `False`
inductive at all, and any proof of `False` in an environment that does yields a proof of this.
-/
def VExpr.false : VExpr := .forallE (.sort .zero) (.bvar 0)

/-- An environment is consistent when it proves no closed instance of `∀ (p : Prop), p`, in any
number `U` of universe parameters. -/
def Consistent (env : VEnv) : Prop := ∀ U e, ¬ env.HasType U [] e VExpr.false

/-! ## Why the axioms must be isolated -/

private def falseAxiom : VConstVal where
  name := `Lean4LeanModel.falseAxiom
  uvars := 0
  type := VExpr.false

/--
Well-formedness alone never implies consistency: an environment may declare `∀ (p : Prop), p` as
an axiom. So consistency can only ever be stated relative to what an environment is allowed to
assume, which is what `ExtendsAxioms` pins down.

(From https://github.com/digama0/lean4lean-model/pull/1.)
-/
theorem exists_inconsistent_wf_environment :
    ∃ env : VEnv, env.WF ∧ ¬ Consistent env := by
  have hfalse : VConstant.WF .empty falseAxiom.toVConstant :=
    ⟨.imax (.succ .zero) .zero, .forallEDF (.sortDF (by trivial) (by trivial) rfl) (.bvar .zero)⟩
  have hadd : ∃ env, VEnv.empty.addConst falseAxiom.name falseAxiom.toVConstant = some env := by
    simp [VEnv.addConst, VEnv.empty]
  obtain ⟨env, hadd⟩ := hadd
  refine ⟨env, ⟨[.axiom falseAxiom], .decl (.axiom hfalse hadd) .empty⟩, fun H => ?_⟩
  exact H 0 (.const falseAxiom.name []) <|
    .constDF (VEnv.addConst_self hadd) (by simp) (by simp) (by simp [falseAxiom]) .nil

/--
There are `ω` inaccessible cardinals: a strictly increasing `ℕ`-indexed sequence of them, one to
interpret each Lean universe `Sort 0, Sort 1, ...`.

Lean itself cannot prove this: its foundations give only `v`-many inaccessibles in universe `v`
(`Cardinal.IsInaccessible.univ`), i.e. a numeral's worth for any fixed universe, never `ω` of
them in a single `Cardinal.{u}`. That gap is exactly the consistency strength assumed by the
model constructions, and is why this is a hypothesis rather than a lemma.
-/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

end Lean4LeanModel
