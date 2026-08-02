import Lean4LeanModel.Consistency

/-!
# Models

A model of a `VEnv` -- an interpretation of its universes, types, terms and constants validating
the typing judgment -- and the two theorems that carry all the weight:

* `Model.extend`: a model of a base environment extends to a model of any environment that
  assumes nothing beyond it. This is where definitions, quotients and inductives are interpreted,
  and it is indifferent to which axioms the base declares.
* `Model.consistent`: a model refutes `∀ (p : Prop), p`.

Each base then needs one model built by hand -- `emptyModel` and `leanAxiomModel` -- and the
headline consistency theorems are corollaries.

Splitting it this way keeps the axioms out of the inductive-and-definition work entirely: the only
place `propext`, `Quot.sound` and `Classical.choice` are ever looked at is `leanAxiomModel`.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/--
A model of `env`.

To be defined: an interpretation of `VLevel` into cardinals below the assumed inaccessibles, of
`VExpr` into that hierarchy, and of `env`'s constants, such that `VEnv.HasType` and
`VEnv.IsDefEq` hold of the interpretations. `Type 1` is a placeholder; the real definition fixes
the universe.
-/
def Model (env : VEnv) : Type 1 := sorry

/--
**Extension.** A model of `base` extends to a model of any environment that assumes nothing
beyond `base`.

Everything that is not an axiom is interpreted here: `def`, `opaque` and `example` carry a value,
`quot` adds the quotient constants and their computation rule, and `induct` is constrained by
`VInductDecl.WF`. The inductive case is blocked upstream, where `VInductDecl.WF` and
`VEnv.addInduct` are still `sorry` and so supply nothing to interpret.
-/
def Model.extend {base env : VEnv} (_ : Model base) (_ : ExtendsAxioms base env) : Model env :=
  sorry

/-- **Soundness.** An environment with a model proves no closed instance of `∀ (p : Prop), p`:
the interpretation of such a proof would inhabit the interpretation of `∀ (p : Prop), p`, which is
empty because `Prop` is interpreted two-valued and proof-irrelevantly. -/
theorem Model.consistent {env : VEnv} (_ : Model env) : Consistent env := by
  sorry

/-! ## The two bases -/

/-- The empty environment has a model: the universe hierarchy alone, interpreting no constants. -/
def emptyModel (_ : OmegaInaccessibles.{u}) : Model .empty := sorry

/--
**Lean's axioms have a model.** `Sort n` is interpreted by the `n`-th inaccessible, `Prop`
two-valued and proof-irrelevantly, which validates `propext`; `Quot` by quotients, which validates
`Quot.sound`; and `Classical.choice` by choice in the metatheory.

This is the only place the axioms are inspected.
-/
def leanAxiomModel (_ : OmegaInaccessibles.{u}) : Model leanAxiomEnv := sorry

/-! ## The headline theorems -/

/--
**Consistency of the axiom-free fragment.** An environment that declares no axioms at all proves
no falsehood.
-/
theorem consistent_of_axiomFree (h : OmegaInaccessibles.{u}) {env : VEnv}
    (hext : ExtendsAxioms .empty env) : Consistent env :=
  ((emptyModel h).extend hext).consistent

/--
**Consistency of Lean.** An environment whose axioms are Lean's three -- `propext`, `Quot.sound`
and `Classical.choice` -- and which otherwise only defines things, proves no falsehood.
-/
theorem consistency (h : OmegaInaccessibles.{u}) {env : VEnv}
    (hext : ExtendsAxioms leanAxiomEnv env) : Consistent env :=
  ((leanAxiomModel h).extend hext).consistent

end Lean4LeanModel
