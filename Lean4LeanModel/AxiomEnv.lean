import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.Meta
import Lean4LeanModel.ExtendsAxioms

/-!
# The Lean 4 axiom environment

A concrete `VEnv` holding exactly what Lean assumes: `propext`, `Quot.sound` and
`Classical.choice`, together with the constants their types mention.

The dependency constants are part of the base on purpose. Pinning only the axioms' types would be
unsound: `Classical.choice : Nonempty α → α` says nothing until `Nonempty` is pinned, and an
environment is free to declare a constant of that name and type meaning something else. So the
base also fixes the introduction and elimination rules of `Eq`, `Iff` and `Nonempty`, which
determine them up to isomorphism.

Everything here is obtained from the real Lean declarations through `Lean4Lean.Theory.Meta`'s
`vconst(type_of% ...)`, so the types cannot drift from Lean's.
-/

namespace Lean4LeanModel

open Lean4Lean

private def cval (name : Name) (c : VConstant) : VConstVal := { toVConstant := c, name }

/-! ## Equality -/

def eqDecl : VConstVal := cval ``Eq vconst(type_of% @Eq)
def eqReflDecl : VConstVal := cval ``Eq.refl vconst(type_of% @Eq.refl)
def eqRecDecl : VConstVal := cval ``Eq.rec vconst(type_of% @Eq.rec)
def eqDefEq : VDefEq := vdefeq(α a motive m => @Eq.rec α a motive m a (Eq.refl a) ≡ m)

/-! ## Iff -/

def iffDecl : VConstVal := cval ``Iff vconst(type_of% @Iff)
def iffIntroDecl : VConstVal := cval ``Iff.intro vconst(type_of% @Iff.intro)
def iffRecDecl : VConstVal := cval ``Iff.rec vconst(type_of% @Iff.rec)
def iffDefEq : VDefEq := vdefeq(a b motive f mp mpr => @Iff.rec a b motive f (Iff.intro mp mpr) ≡ f mp mpr)

/-! ## Nonempty -/

def nonemptyDecl : VConstVal := cval ``Nonempty vconst(type_of% @Nonempty)
def nonemptyIntroDecl : VConstVal := cval ``Nonempty.intro vconst(type_of% @Nonempty.intro)
def nonemptyRecDecl : VConstVal := cval ``Nonempty.rec vconst(type_of% @Nonempty.rec)

/-! ## Quotients

The quotient constants and the `Quot.lift` computation rule come from upstream's `VEnv.addQuot`;
`Quot.sound` is not among them, being an axiom.
-/

def quotDecl : VConstVal := cval ``Quot quotConst
def quotMkDecl : VConstVal := cval ``Quot.mk quotMkConst
def quotLiftDecl : VConstVal := cval ``Quot.lift quotLiftConst
def quotIndDecl : VConstVal := cval ``Quot.ind quotIndConst

/-! ## The axioms -/

def propextDecl : VConstVal := cval ``propext vconst(type_of% @propext)
def quotSoundDecl : VConstVal := cval ``Quot.sound vconst(type_of% @Quot.sound)
def choiceDecl : VConstVal := cval ``Classical.choice vconst(type_of% @Classical.choice)

/-- Lean's three axioms. -/
def leanAxioms : List VConstVal := [propextDecl, quotSoundDecl, choiceDecl]

/-- The constants that the axioms' types depend on, with their rules. -/
def leanAxiomDeps : List VConstVal :=
  [eqDecl, eqReflDecl, eqRecDecl,
   iffDecl, iffIntroDecl, iffRecDecl,
   nonemptyDecl, nonemptyIntroDecl, nonemptyRecDecl,
   quotDecl, quotMkDecl, quotLiftDecl, quotIndDecl]

def leanAxiomConstants : List VConstVal := leanAxiomDeps ++ leanAxioms

/--
The computation rules of the base.

`quotDefEq` is upstream's; the three `rec` rules are stated in the shape the corresponding Lean
recursors have. Since environments are built *from* this base rather than checked against it,
nothing has to reproduce these -- they hold by construction. Their shape matters only for a future
bridging result identifying a real environment, built from `VEnv.empty` with `Eq` and friends
declared as inductives, with an extension of this base; that comparison needs the `VDefEq`s
emitted by `VEnv.addInduct`, still `sorry` upstream.
-/
def leanAxiomDefEqs : List VDefEq := [quotDefEq, eqDefEq, iffDefEq]

/--
The Lean 4 axiom environment: the three axioms plus the constants and computation rules that give
their types meaning. Consistency of the real environment is reduced to consistency of this one.

The `constants` field is a list lookup, so membership is decidable -- an environment can be
checked against this base declaration by declaration.
-/
def leanAxiomEnv : VEnv where
  constants n := (leanAxiomConstants.find? (·.name == n)).map (·.toVConstant)
  defeqs df := df ∈ leanAxiomDefEqs

end Lean4LeanModel
