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

To be defined. Whatever the definition ends up being, it has to supply enough structure to
validate the judgments of `env` (`VEnv.HasType`, `VEnv.IsDefEq`), and nothing more.

In particular it does *not* require non-degeneracy, following the usual practice in categorical
semantics: the trivial model -- every type interpreted as terminal -- is a model of any type
theory, and is the terminal object in the category of models, so a class of models closed under
the constructions one actually uses has to contain it. "Has a model" is therefore vacuous on its
own; consistency comes from a model that additionally satisfies `Nondegenerate` below. This is
unlike first-order logic, where satisfaction of `⊥` is false by definition of satisfaction and so
every structure is non-degenerate for free. The syntactic model makes the point: it is
non-degenerate exactly when the theory is consistent, so initiality alone never gives consistency.

Deliberately *not* part of it: sets, cardinality, or any commitment that `∀ (x : α), β` is
interpreted by the full function space. A term model -- syntax quotiented by definitional
equality -- and countable models where the interpretation of a function type is some subset of
the functions must both qualify. Pinning the notion to ZFC function spaces would rule those out
for no gain: the set-theoretic hierarchy is how `leanAxiomModel` is expected to be built, but that
is a fact about one construction, not about what a model is.

Written point-free (`VEnv → Type _` rather than a parameter to the left of the colon) so that the
placeholder still depends on its argument: with `def Model (env : VEnv) := sorry` the body ignores
`env` and every `Model env` is definitionally the same type.
-/
def Model : VEnv → Type (u+1) := sorry

/--
A model is non-degenerate when it interprets `∀ (p : Prop), p` by something uninhabited.

To be defined alongside `Model`. Since every type theory has the trivial model, this -- and not
the existence of a model -- is what carries consistency.
-/
def Model.Nondegenerate {env : VEnv} : Model.{u} env → Prop := sorry

/-- **Soundness.** An environment with a non-degenerate model proves no closed instance of
`∀ (p : Prop), p`: a closed proof would be interpreted as an element of the interpretation of that
type, which `Nondegenerate` says is empty. -/
theorem Model.consistent {env : VEnv} (m : Model.{u} env) (_ : m.Nondegenerate) :
    Consistent env := by
  sorry

/--
**Extension.** A model of `base` extends to a model of any environment that assumes nothing
beyond `base`.

`ExtendsAxioms` only asks that `env` add no axioms to some `base' ≤ base`, so the first move is to
restrict the model to `base'` -- soundness is monotonic in that direction, there being less to
interpret and less to validate.

Everything that is not an axiom is interpreted here: `def`, `opaque` and `example` carry a value,
`quot` adds the quotient constants and their computation rule, and `induct` is constrained by
`VInductDecl.WF`. The inductive case is blocked upstream, where `VInductDecl.WF` and
`VEnv.addInduct` are still `sorry` and so supply nothing to interpret.
-/
def Model.extend {base env : VEnv} (_ : Model.{u} base) (_ : ExtendsAxioms base env) :
    Model.{u} env := sorry

/--
**Extension is conservative.** Interpreting further definitions, quotients and inductives does not
make `∀ (p : Prop), p` inhabited.

This is a separate obligation on purpose. Folding non-degeneracy into `Model` would hide it inside
`Model.extend`, where it is easy to overlook -- and it is not a bookkeeping step: it is the reason
a definitional extension cannot prove anything new.
-/
theorem Model.extend_nondegenerate {base env : VEnv} (m : Model.{u} base)
    (h : ExtendsAxioms base env) (_ : m.Nondegenerate) : (m.extend h).Nondegenerate := by
  sorry

/-! ## The two bases -/

/--
The empty environment has a model: the universe hierarchy alone, interpreting no constants.

The inaccessibles are assumed here because a set-theoretic model needs them. A term model would
not -- it would need normalization instead -- so if that route is taken this hypothesis can be
dropped, strengthening `consistent_of_axiomFree` to hold outright.
-/
def emptyModel (_ : OmegaInaccessibles.{u}) : Model.{u} .empty := sorry

theorem emptyModel_nondegenerate (h : OmegaInaccessibles.{u}) : (emptyModel h).Nondegenerate := by
  sorry

/--
**Lean's axioms have a model.** The construction in mind is set-theoretic: `Sort n` interpreted by
the `n`-th inaccessible, `Prop` two-valued and proof-irrelevantly (validating `propext`), `Quot`
by quotients (validating `Quot.sound`), and `Classical.choice` by choice in the metatheory. Any
other structure meeting `Model` would do just as well.

This is the only place the axioms are inspected.
-/
def leanAxiomModel (_ : OmegaInaccessibles.{u}) : Model.{u} leanAxiomEnv := sorry

/-- Lean's axioms are not merely modeled but consistently so: the set-theoretic interpretation
sends `∀ (p : Prop), p` to the empty set. -/
theorem leanAxiomModel_nondegenerate (h : OmegaInaccessibles.{u}) :
    (leanAxiomModel h).Nondegenerate := by
  sorry

/-! ## The headline theorems -/

/--
**Consistency of the axiom-free fragment.** An environment that declares no axioms at all proves
no falsehood.
-/
theorem consistent_of_axiomFree (h : OmegaInaccessibles.{u}) {env : VEnv}
    (hext : ExtendsAxioms .empty env) : Consistent env :=
  ((emptyModel h).extend hext).consistent <|
    (emptyModel h).extend_nondegenerate hext (emptyModel_nondegenerate h)

/--
**Consistency of Lean.** An environment whose axioms are Lean's three -- `propext`, `Quot.sound`
and `Classical.choice` -- and which otherwise only defines things, proves no falsehood.
-/
theorem consistency (h : OmegaInaccessibles.{u}) {env : VEnv}
    (hext : ExtendsAxioms leanAxiomEnv env) : Consistent env :=
  ((leanAxiomModel h).extend hext).consistent <|
    (leanAxiomModel h).extend_nondegenerate hext (leanAxiomModel_nondegenerate h)

end Lean4LeanModel
