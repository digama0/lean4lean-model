import Lean4LeanModel.DeclarationPolicy
import Lean4Lean.Theory.Typing.Lemmas
import Mathlib.SetTheory.Cardinal.Regular

/-!
# The target theorem

Consistency of Lean's standard fragment, relative to the existence of `ω` inaccessible cardinals --
the first model theorem toward the soundness theorem of *The Type Theory of Lean*.

The type theory itself is the one formalized in `Lean4Lean.Theory`: `VExpr` is the term syntax,
`VEnv` the declaration environment, `StandardWF` says the environment was built by well-founded
declarations (`VDecl.WF`) admitting the canonical `Eq`, `Iff`, and `Nonempty` inductives and Lean's
three standard axioms, and `VEnv.HasType` is the typing judgment. Primitive quotient declarations
remain in scope.

The model construction is what fills the remaining `sorry` in the consistency theorem.
General inductive declarations await the completion of `VInductDecl.WF` and `VEnv.addInduct`
upstream in lean4lean. The standard fragment fixes the exact declarations needed by the axioms so
their special cases can be modeled directly.
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

/-! ## Why the axiom restriction is necessary -/

private def falseAxiom : VConstVal where
  name := `Lean4LeanModel.falseAxiom
  uvars := 0
  type := VExpr.false

/-- Unrestricted well-formed environments are not consistent: they may declare
`∀ (p : Prop), p` as an axiom. This is the counterexample that necessitates excluding axiom
declarations from the initial target theorem. -/
theorem exists_inconsistent_wf_environment :
    ∃ (env : VEnv), env.WF ∧ ∃ e, env.HasType 0 [] e VExpr.false := by
  have hfalse : VConstant.WF .empty falseAxiom.toVConstant := by
    refine ⟨.imax (.succ .zero) .zero, ?_⟩
    exact .forallEDF (.sortDF (by trivial) (by trivial) rfl) (.bvar .zero)
  have hadd : ∃ env, VEnv.empty.addConst falseAxiom.name falseAxiom.toVConstant = some env := by
    simp [VEnv.addConst, VEnv.empty]
  obtain ⟨env, hadd⟩ := hadd
  refine ⟨env, ⟨[.axiom falseAxiom], .decl (.axiom hfalse hadd) .empty⟩, ?_⟩
  refine ⟨.const falseAxiom.name [], ?_⟩
  exact .constDF (VEnv.addConst_self hadd) (by simp) (by simp) (by simp [falseAxiom]) .nil

/--
There are `ω` inaccessible cardinals: a strictly increasing `ℕ`-indexed sequence of them, one to
interpret each Lean universe `Sort 0, Sort 1, ...`.

Lean itself cannot prove this: its foundations give only `v`-many inaccessibles in universe `v`
(`Cardinal.IsInaccessible.univ`), i.e. a numeral's worth for any fixed universe, never `ω` of
them in a single `Cardinal.{u}`. That gap is exactly the consistency strength the theorem below
assumes, and is why this is a hypothesis rather than a lemma.
-/
def OmegaInaccessibles : Prop :=
  ∃ κ : ℕ → Cardinal.{u}, StrictMono κ ∧ ∀ n, (κ n).IsInaccessible

/--
**Consistency of the standard fragment.** Assuming `ω` inaccessible cardinals, no standard
well-formed environment proves `∀ (p : Prop), p` -- in any number `U` of universe parameters, in
the empty local context. The fragment includes the canonical `Eq`, `Iff`, and `Nonempty`
inductives, primitive quotients, and exactly Lean's three standard axioms: `propext`,
`Classical.choice`, and `Quot.sound`.
-/
theorem consistency (_ : OmegaInaccessibles.{u}) {env : VEnv} (_ : StandardWF env) (U : Nat) :
    ¬ ∃ e, env.HasType U [] e VExpr.false := by
  sorry

end Lean4LeanModel
