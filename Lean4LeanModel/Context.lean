import Lean4LeanModel.Semantics

/-!
# Modeled local contexts

A valuation is built from the outside in.  At each binder, its semantic value must inhabit the
interpretation of the binder type under the already-modeled tail.  Keeping this relation separate
from syntactic context well-formedness makes the induction hypotheses used by soundness explicit.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- A semantic valuation for a dependent local context. -/
inductive ModelsCtx (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) : List VExpr → List ZFSet.{u} → Prop
  | nil : ModelsCtx κ env assignment L [] []
  | cons {Γ γ A x} :
      ModelsCtx κ env assignment L Γ γ →
      x ∈ interp κ env assignment L Γ γ A →
      ModelsCtx κ env assignment L (A :: Γ) (x :: γ)

namespace ModelsCtx

@[simp]
theorem nil_iff {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {γ : List ZFSet.{u}} :
    ModelsCtx κ env assignment L [] γ ↔ γ = [] := by
  constructor
  · intro h
    cases h
    rfl
  · rintro rfl
    exact .nil

theorem tail {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {x : ZFSet.{u}} :
    ModelsCtx κ env assignment L (A :: Γ) (x :: γ) →
    ModelsCtx κ env assignment L Γ γ
  | .cons h _ => h

theorem head_mem {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {x : ZFSet.{u}}
    (h : ModelsCtx κ env assignment L (A :: Γ) (x :: γ)) :
    x ∈ interp κ env assignment L Γ γ A := by
  cases h with
  | cons _ hx => exact hx

theorem cons_iff {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} :
    ModelsCtx κ env assignment L (A :: Γ) γ ↔
      ∃ x γ', γ = x :: γ' ∧ ModelsCtx κ env assignment L Γ γ' ∧
        x ∈ interp κ env assignment L Γ γ' A := by
  constructor
  · intro h
    cases h with
    | cons hγ hx => exact ⟨_, _, rfl, hγ, hx⟩
  · rintro ⟨x, γ', rfl, hγ, hx⟩
    exact .cons hγ hx

theorem length_eq {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}}
    (h : ModelsCtx κ env assignment L Γ γ) : γ.length = Γ.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem exists_nil {κ : ℕ → Cardinal.{u}} (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) : ∃ γ, ModelsCtx κ env assignment L [] γ :=
  ⟨[], .nil⟩

/-- Extend a modeled context by any semantic inhabitant of the next binder type. -/
theorem extend {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr}
    (hγ : ModelsCtx κ env assignment L Γ γ) {x : ZFSet.{u}}
    (hx : x ∈ interp κ env assignment L Γ γ A) :
    ModelsCtx κ env assignment L (A :: Γ) (x :: γ) :=
  .cons hγ hx

end ModelsCtx

/-- The syntactic and semantic halves of a well-formed modeled context. -/
structure ContextModel (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) : Prop where
  syntaxWF : OnCtx Γ (env.IsType L.length)
  valuation : ModelsCtx κ env assignment L Γ γ

namespace ContextModel

theorem nil (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) : ContextModel κ env assignment L [] [] :=
  ⟨trivial, .nil⟩

theorem extend {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {lvl : VLevel}
    (h : ContextModel κ env assignment L Γ γ)
    (hA : env.HasType L.length Γ A (.sort lvl)) {x : ZFSet.{u}}
    (hx : x ∈ interp κ env assignment L Γ γ A) :
    ContextModel κ env assignment L (A :: Γ) (x :: γ) :=
  ⟨⟨h.syntaxWF, lvl, hA⟩, h.valuation.extend hx⟩

theorem tail {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {x : ZFSet.{u}}
    (h : ContextModel κ env assignment L (A :: Γ) (x :: γ)) :
    ContextModel κ env assignment L Γ γ :=
  ⟨h.syntaxWF.1, h.valuation.tail⟩

theorem head_isType {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {x : ZFSet.{u}}
    (h : ContextModel κ env assignment L (A :: Γ) (x :: γ)) :
    env.IsType L.length Γ A :=
  h.syntaxWF.2

theorem head_mem {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {x : ZFSet.{u}}
    (h : ContextModel κ env assignment L (A :: Γ) (x :: γ)) :
    x ∈ interp κ env assignment L Γ γ A :=
  h.valuation.head_mem

theorem length_eq {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    {L : List Nat} {Γ : List VExpr} {γ : List ZFSet.{u}}
    (h : ContextModel κ env assignment L Γ γ) : γ.length = Γ.length :=
  h.valuation.length_eq

end ContextModel

section SanityChecks

variable (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u}) (L : List Nat)

example : ModelsCtx κ env assignment L [] [] := .nil

example {Γ : List VExpr} {γ : List ZFSet.{u}} {A : VExpr} {x : ZFSet.{u}}
    (hγ : ModelsCtx κ env assignment L Γ γ)
    (hx : x ∈ interp κ env assignment L Γ γ A) :
    (x :: γ).length = (A :: Γ).length :=
  (hγ.extend hx).length_eq

end SanityChecks

end Lean4LeanModel
