import Lean4Lean.Theory.Typing.Env

/-!
# The standard declaration fragment

`Lean4Lean.VEnv.WF` permits arbitrary well-typed axioms, so consistency requires a more precise
description of the declaration histories in scope.  The fragment below admits ordinary
definitions, opaque definitions, examples, and primitive quotients, together with the standard
inductive declarations on which Lean's three standard axioms depend.

The standard names are reserved: an ordinary definition cannot install a different `Eq`, `Iff`,
or `Nonempty` with the expected type.  Each standard axiom is admitted only with its exact name and
type, after its dependencies have been installed by the corresponding canonical declaration.
-/

namespace Lean4LeanModel

open Lean4Lean

/-- Attach a name to the type of a Lean constant translated to `VExpr`. -/
private def namedConstant (name : Name) (ci : VConstant) : VConstVal where
  name := name
  uvars := ci.uvars
  type := ci.type

def standardEq : VConstVal := namedConstant ``Eq vconst(type_of% @Eq)
def standardEqRefl : VConstVal := namedConstant ``Eq.refl vconst(type_of% @Eq.refl)
def standardIff : VConstVal := namedConstant ``Iff vconst(type_of% @Iff)
def standardIffIntro : VConstVal := namedConstant ``Iff.intro vconst(type_of% @Iff.intro)
def standardNonempty : VConstVal := namedConstant ``Nonempty vconst(type_of% @Nonempty)
def standardNonemptyIntro : VConstVal :=
  namedConstant ``Nonempty.intro vconst(type_of% @Nonempty.intro)

/-- The canonical declaration of propositional equality. -/
def standardEqDecl : VInductDecl where
  uvars := 1
  nparams := 2
  types := [{ toVConstVal := standardEq, ctors := [standardEqRefl] }]

/-- The canonical declaration of logical equivalence. -/
def standardIffDecl : VInductDecl where
  uvars := 0
  nparams := 2
  types := [{ toVConstVal := standardIff, ctors := [standardIffIntro] }]

/-- The canonical declaration of propositional nonemptiness. -/
def standardNonemptyDecl : VInductDecl where
  uvars := 1
  nparams := 1
  types := [{ toVConstVal := standardNonempty, ctors := [standardNonemptyIntro] }]

def standardPropext : VConstVal := namedConstant ``propext vconst(type_of% @propext)
def standardChoice : VConstVal :=
  namedConstant ``Classical.choice vconst(type_of% @Classical.choice)
def standardQuotSound : VConstVal := namedConstant ``Quot.sound vconst(type_of% @Quot.sound)

/-- The names whose meanings are fixed by the standard prelude.  Reserving the generated recursor
names as well as the type and constructor names prevents an earlier declaration from changing the
meaning or computation behavior of a later standard inductive declaration. -/
def StandardName (name : Name) : Prop :=
  name = ``Eq ∨ name = ``Eq.refl ∨ name = ``Eq.rec ∨
  name = ``Iff ∨ name = ``Iff.intro ∨ name = ``Iff.rec ∨
  name = ``Nonempty ∨ name = ``Nonempty.intro ∨ name = ``Nonempty.rec ∨
  name = ``Quot ∨ name = ``Quot.mk ∨ name = ``Quot.lift ∨ name = ``Quot.ind ∨
  name = ``propext ∨ name = ``Classical.choice ∨ name = ``Quot.sound

/-- The environment contains this exact named constant.  In a `StandardWF` history, reserved-name
discipline ensures that such a constant came from its canonical standard declaration. -/
def HasStandardConstant (env : VEnv) (ci : VConstVal) : Prop :=
  env.constants ci.name = some ci.toVConstant

/-- Exactly the three standard axioms, with the standard meanings of every constant used in their
types checked in the environment in which the axiom is introduced. -/
def StandardAxiom (env : VEnv) (ci : VConstVal) : Prop :=
  (ci = standardPropext ∧
      HasStandardConstant env standardEq ∧ HasStandardConstant env standardIff) ∨
  (ci = standardChoice ∧ HasStandardConstant env standardNonempty) ∨
  (ci = standardQuotSound ∧
      HasStandardConstant env standardEq ∧
      HasStandardConstant env (namedConstant ``Quot quotConst) ∧
      HasStandardConstant env (namedConstant ``Quot.mk quotMkConst))

/-- The three inductive declarations whose meanings are required by the standard axioms. -/
def StandardInductive (decl : VInductDecl) : Prop :=
  decl = standardEqDecl ∨ decl = standardIffDecl ∨ decl = standardNonemptyDecl

/-- Declarations supported by the standard fragment.  The exhaustive match is deliberate: a new
upstream declaration form must be reviewed before it enters the modeled fragment. -/
def StandardDecl (env : VEnv) : VDecl → Prop
  | .block _ => False
  | .axiom ci => StandardAxiom env ci
  | .def ci => ¬ StandardName ci.name
  | .opaque ci => ¬ StandardName ci.name
  | .example _ => True
  | .quot => True
  | .induct decl => StandardInductive decl

/-- An environment constructed entirely from declarations in the standard fragment.  Making the
policy depend on the preceding environment lets an axiom case carry evidence that its standard
dependencies have already been installed. -/
inductive StandardWF : VEnv → Prop where
  | empty : StandardWF .empty
  | decl : StandardWF env → VDecl.WF env d env' → StandardDecl env d → StandardWF env'

/-- Forgetting the standard-declaration policy leaves ordinary environment well-formedness. -/
theorem StandardWF.wf : StandardWF env → env.WF
  | .empty => ⟨[], .empty⟩
  | .decl h hd _ =>
    let ⟨ds, hds⟩ := h.wf
    ⟨_ :: ds, .decl hd hds⟩

end Lean4LeanModel
