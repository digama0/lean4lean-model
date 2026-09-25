import Lean4LeanModel.DependentFunction
import Lean4LeanModel.Upstream
import Lean4Lean.Theory.Typing.EnvLemmas
import Mathlib.Data.List.GetD

/-!
# Proof-split interpretation

The classification predicates are total on raw syntax. Their values are canonical on well-typed
terms by the isolated zero/nonzero unique-typing result in `Lean4LeanModel.Upstream`.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- `∀ (p : Prop), p`, an environment-independent false proposition. -/
def VExpr.false : VExpr := .forallE (.sort .zero) (.bvar 0)

/-- A type expression is proposition-valued at the supplied universe valuation. -/
def IsPropType (env : VEnv) (U : Nat) (Γ : List VExpr) (L : List Nat) (A : VExpr) : Prop :=
  ∃ l, env.HasType U Γ A (.sort l) ∧ l.eval L = 0

/-- A term is a proof when its type is proposition-valued. -/
def IsProofTerm (env : VEnv) (U : Nat) (Γ : List VExpr) (L : List Nat) (e : VExpr) : Prop :=
  ∃ A, env.HasType U Γ e A ∧ IsPropType env U Γ L A

/-- Turn the proof/type split into the universe discriminator consumed by stage-2 operations. -/
noncomputable def classLevel (p : Prop) : Nat := by
  classical
  exact if p then 0 else 1

@[simp]
theorem classLevel_eq_zero {p : Prop} : classLevel p = 0 ↔ p := by
  classical
  simp [classLevel]

@[simp]
theorem classLevel_ne_zero {p : Prop} : classLevel p ≠ 0 ↔ ¬p := by
  rw [Ne, classLevel_eq_zero]

/-- The Prop/Type discriminator for a raw type expression. -/
noncomputable def typeClass (env : VEnv) (Γ : List VExpr) (L : List Nat) (A : VExpr) : Nat :=
  classLevel (IsPropType env L.length Γ L A)

/-- The proof/data discriminator for a raw term expression. -/
noncomputable def termClass (env : VEnv) (Γ : List VExpr) (L : List Nat) (e : VExpr) : Nat :=
  classLevel (IsProofTerm env L.length Γ L e)

/-- Total dispatch defaults to data outside a well-formed syntactic context. -/
noncomputable def safeTypeClass (env : VEnv) (Γ : List VExpr) (L : List Nat) (A : VExpr) : Nat :=
  by classical exact if OnCtx Γ (env.IsType L.length) then typeClass env Γ L A else 1

/-- Total dispatch defaults to data outside a well-formed syntactic context. -/
noncomputable def safeTermClass (env : VEnv) (Γ : List VExpr) (L : List Nat) (e : VExpr) : Nat :=
  by classical exact if OnCtx Γ (env.IsType L.length) then termClass env Γ L e else 1

theorem safeTypeClass_eq (hΓ : OnCtx Γ (env.IsType L.length)) :
    safeTypeClass env Γ L A = typeClass env Γ L A := by
  simp [safeTypeClass, hΓ]

theorem safeTermClass_eq (hΓ : OnCtx Γ (env.IsType L.length)) :
    safeTermClass env Γ L e = termClass env Γ L e := by
  simp [safeTermClass, hΓ]

@[simp]
theorem typeClass_eq_zero {env : VEnv} {Γ : List VExpr} {L : List Nat} {A : VExpr} :
    typeClass env Γ L A = 0 ↔ IsPropType env L.length Γ L A := by
  exact classLevel_eq_zero

@[simp]
theorem termClass_eq_zero {env : VEnv} {Γ : List VExpr} {L : List Nat} {e : VExpr} :
    termClass env Γ L e = 0 ↔ IsProofTerm env L.length Γ L e := by
  exact classLevel_eq_zero

theorem isPropType_iff_of_hasType {env : VEnv} {U : Nat} {Γ : List VExpr}
    {L : List Nat} {A : VExpr} {u : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) :
    IsPropType env U Γ L A ↔ u.eval L = 0 := by
  constructor
  · rintro ⟨v, hA', hv⟩
    exact (Upstream.propSort_eval_eq henv hΓ hA hA' L).trans hv
  · exact fun hu => ⟨u, hA, hu⟩

theorem isProofTerm_iff_of_hasType {env : VEnv} {U : Nat} {Γ : List VExpr}
    {L : List Nat} {e A : VExpr} {u : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (he : env.HasType U Γ e A) (hA : env.HasType U Γ A (.sort u)) :
    IsProofTerm env U Γ L e ↔ u.eval L = 0 := by
  constructor
  · rintro ⟨B, heB, v, hB, hv⟩
    exact (Upstream.termSort_eval_eq henv hΓ he hA heB hB L).trans hv
  · exact fun hu => ⟨A, he, u, hA, hu⟩

theorem typeClass_eq_zero_iff_of_hasType {env : VEnv} {Γ : List VExpr}
    {L : List Nat} {A : VExpr} {u : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hA : env.HasType L.length Γ A (.sort u)) :
    typeClass env Γ L A = 0 ↔ u.eval L = 0 := by
  rw [typeClass_eq_zero, isPropType_iff_of_hasType henv hΓ hA]

theorem termClass_eq_zero_iff_of_hasType {env : VEnv} {Γ : List VExpr}
    {L : List Nat} {e A : VExpr} {u : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (he : env.HasType L.length Γ e A) (hA : env.HasType L.length Γ A (.sort u)) :
    termClass env Γ L e = 0 ↔ u.eval L = 0 := by
  rw [termClass_eq_zero, isProofTerm_iff_of_hasType henv hΓ he hA]

/-- A term and its type have the same proof/Prop class. -/
theorem termClass_eq_typeClass_of_hasType {env : VEnv} {Γ : List VExpr}
    {L : List Nat} {e A : VExpr} {u : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (he : env.HasType L.length Γ e A) (hA : env.HasType L.length Γ A (.sort u)) :
    termClass env Γ L e = typeClass env Γ L A := by
  unfold termClass typeClass
  apply congrArg classLevel
  apply propext
  rw [isProofTerm_iff_of_hasType henv hΓ he hA,
    isPropType_iff_of_hasType henv hΓ hA]

/-- A dependent product is proposition-valued exactly when its codomain is. -/
theorem typeClass_forallE {env : VEnv} {Γ : List VExpr} {L : List Nat}
    {A B : VExpr} {u v : VLevel} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType L.length))
    (hA : env.HasType L.length Γ A (.sort u))
    (hB : env.HasType L.length (A :: Γ) B (.sort v)) :
    typeClass env Γ L (.forallE A B) = typeClass env (A :: Γ) L B := by
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA⟩
  have hAB : env.HasType L.length Γ (.forallE A B) (.sort (.imax u v)) :=
    .forallEDF hA hB
  unfold typeClass
  apply congrArg classLevel
  apply propext
  rw [isPropType_iff_of_hasType henv hΓ hAB,
    isPropType_iff_of_hasType henv hΓA hB]
  change Nat.imax (u.eval L) (v.eval L) = 0 ↔ v.eval L = 0
  unfold Nat.imax
  split <;> simp_all

/-- An abstraction has the same proof/data class as its body. -/
theorem termClass_lam {env : VEnv} {Γ : List VExpr} {L : List Nat}
    {A B body : VExpr} {u v : VLevel} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType L.length))
    (hA : env.HasType L.length Γ A (.sort u))
    (hbody : env.HasType L.length (A :: Γ) body B)
    (hB : env.HasType L.length (A :: Γ) B (.sort v)) :
    termClass env Γ L (.lam A body) = termClass env (A :: Γ) L body := by
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA⟩
  have hAB : env.HasType L.length Γ (.forallE A B) (.sort (.imax u v)) :=
    .forallEDF hA hB
  calc
    termClass env Γ L (.lam A body) = typeClass env Γ L (.forallE A B) :=
      termClass_eq_typeClass_of_hasType henv hΓ (.lamDF hA hbody) hAB
    _ = typeClass env (A :: Γ) L B := typeClass_forallE henv hΓ hA hB
    _ = termClass env (A :: Γ) L body :=
      (termClass_eq_typeClass_of_hasType henv hΓA hbody hB).symm

theorem IsPropType.mono {env env' : VEnv} {U : Nat} {Γ : List VExpr}
    {L : List Nat} {A : VExpr} (hle : env ≤ env') :
    IsPropType env U Γ L A → IsPropType env' U Γ L A := by
  rintro ⟨u, hA, hu⟩
  exact ⟨u, hA.mono hle, hu⟩

theorem IsProofTerm.mono {env env' : VEnv} {U : Nat} {Γ : List VExpr}
    {L : List Nat} {e : VExpr} (hle : env ≤ env') :
    IsProofTerm env U Γ L e → IsProofTerm env' U Γ L e := by
  rintro ⟨A, he, hA⟩
  exact ⟨A, he.mono hle, hA.mono hle⟩

theorem IsPropType.liftN_iff {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr}
    {L : List Nat} {A : VExpr} (henv : env.WF)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') :
    IsPropType env U Γ' L (A.liftN n k) ↔ IsPropType env U Γ L A := by
  constructor
  · rintro ⟨u, hA, hu⟩
    exact ⟨u, (Upstream.hasType_liftN_sort_iff henv hΓ' W).1 hA, hu⟩
  · rintro ⟨u, hA, hu⟩
    exact ⟨u, (Upstream.hasType_liftN_sort_iff henv hΓ' W).2 hA, hu⟩

theorem IsProofTerm.liftN_iff {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr}
    {L : List Nat} {e : VExpr} (henv : env.WF)
    (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') :
    IsProofTerm env U Γ' L (e.liftN n k) ↔ IsProofTerm env U Γ L e := by
  have hΓ := Upstream.ctx_of_liftN henv hΓ' W
  constructor
  · rintro ⟨A', he', u, hA', hu⟩
    obtain ⟨A, he, heW⟩ := Upstream.strengthen_liftN_typing henv hΓ' W he'
    obtain ⟨v, hA⟩ := he.isType henv hΓ
    have hvu := Upstream.termSort_eval_eq henv hΓ' heW (hA.weakN henv W) he' hA' L
    exact ⟨A, he, v, hA, hvu.trans hu⟩
  · rintro ⟨A, he, u, hA, hu⟩
    exact ⟨A.liftN n k, he.weakN henv W, u, hA.weakN henv W, hu⟩

theorem typeClass_weakN {env : VEnv} {n k : Nat} {Γ Γ' : List VExpr}
    {L : List Nat} {A : VExpr} (henv : env.WF)
    (hΓ' : OnCtx Γ' (env.IsType L.length)) (W : Ctx.LiftN n k Γ Γ') :
    typeClass env Γ' L (A.liftN n k) = typeClass env Γ L A := by
  apply congrArg classLevel
  exact propext (IsPropType.liftN_iff henv hΓ' W)

theorem termClass_weakN {env : VEnv} {n k : Nat} {Γ Γ' : List VExpr}
    {L : List Nat} {e : VExpr} (henv : env.WF)
    (hΓ' : OnCtx Γ' (env.IsType L.length)) (W : Ctx.LiftN n k Γ Γ') :
    termClass env Γ' L (e.liftN n k) = termClass env Γ L e := by
  apply congrArg classLevel
  exact propext (IsProofTerm.liftN_iff henv hΓ' W)

theorem safeTypeClass_weakN {env : VEnv} {n k : Nat} {Γ Γ' : List VExpr}
    {L : List Nat} {A : VExpr} (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (hctx : OnCtx Γ' (env.IsType L.length) ↔ OnCtx Γ (env.IsType L.length)) :
    safeTypeClass env Γ' L (A.liftN n k) = safeTypeClass env Γ L A := by
  classical
  by_cases hΓ' : OnCtx Γ' (env.IsType L.length)
  · have hΓ := hctx.1 hΓ'
    simp [safeTypeClass, hΓ', hΓ, typeClass_weakN henv hΓ' W]
  · have hΓ : ¬OnCtx Γ (env.IsType L.length) := fun h => hΓ' (hctx.2 h)
    simp [safeTypeClass, hΓ', hΓ]

theorem safeTermClass_weakN {env : VEnv} {n k : Nat} {Γ Γ' : List VExpr}
    {L : List Nat} {e : VExpr} (henv : env.WF) (W : Ctx.LiftN n k Γ Γ')
    (hctx : OnCtx Γ' (env.IsType L.length) ↔ OnCtx Γ (env.IsType L.length)) :
    safeTermClass env Γ' L (e.liftN n k) = safeTermClass env Γ L e := by
  classical
  by_cases hΓ' : OnCtx Γ' (env.IsType L.length)
  · have hΓ := hctx.1 hΓ'
    simp [safeTermClass, hΓ', hΓ, termClass_weakN henv hΓ' W]
  · have hΓ : ¬OnCtx Γ (env.IsType L.length) := fun h => hΓ' (hctx.2 h)
    simp [safeTermClass, hΓ', hΓ]

/-- Proposition classification is invariant under definitional equality of types. -/
theorem IsPropType.congr {env : VEnv} {U : Nat} {Γ : List VExpr} {L : List Nat}
    {A A' : VExpr} {u : VLevel} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEq U Γ A A' (.sort u)) :
    IsPropType env U Γ L A ↔ IsPropType env U Γ L A' := by
  rw [isPropType_iff_of_hasType henv hΓ h.hasType.1,
    isPropType_iff_of_hasType henv hΓ h.hasType.2]

/-- Proof classification is invariant under definitional equality of terms. -/
theorem IsProofTerm.congr {env : VEnv} {U : Nat} {Γ : List VExpr} {L : List Nat}
    {e e' A : VExpr} {u : VLevel} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEq U Γ e e' A) (hA : env.HasType U Γ A (.sort u)) :
    IsProofTerm env U Γ L e ↔ IsProofTerm env U Γ L e' := by
  rw [isProofTerm_iff_of_hasType henv hΓ h.hasType.1 hA,
    isProofTerm_iff_of_hasType henv hΓ h.hasType.2 hA]

theorem isPropType_mono_iff {env env' : VEnv} {U : Nat} {Γ : List VExpr}
    {L : List Nat} {A : VExpr} {u : VLevel}
    (hle : env ≤ env') (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (henv' : env'.WF) (hΓ' : OnCtx Γ (env'.IsType U))
    (hA : env.HasType U Γ A (.sort u)) :
    IsPropType env' U Γ L A ↔ IsPropType env U Γ L A := by
  rw [isPropType_iff_of_hasType henv' hΓ' (hA.mono hle),
    isPropType_iff_of_hasType henv hΓ hA]

theorem isProofTerm_mono_iff {env env' : VEnv} {U : Nat} {Γ : List VExpr}
    {L : List Nat} {e A : VExpr} {u : VLevel}
    (hle : env ≤ env') (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (henv' : env'.WF) (hΓ' : OnCtx Γ (env'.IsType U))
    (he : env.HasType U Γ e A) (hA : env.HasType U Γ A (.sort u)) :
    IsProofTerm env' U Γ L e ↔ IsProofTerm env U Γ L e := by
  rw [isProofTerm_iff_of_hasType henv' hΓ' (he.mono hle) (hA.mono hle),
    isProofTerm_iff_of_hasType henv hΓ he hA]

theorem typeClass_congr {env : VEnv} {Γ : List VExpr} {L : List Nat}
    {A A' : VExpr} {u : VLevel} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType L.length))
    (h : env.IsDefEq L.length Γ A A' (.sort u)) :
    typeClass env Γ L A = typeClass env Γ L A' := by
  apply congrArg classLevel
  exact propext (IsPropType.congr henv hΓ h)

theorem termClass_congr {env : VEnv} {Γ : List VExpr} {L : List Nat}
    {e e' A : VExpr} {u : VLevel} (henv : env.WF)
    (hΓ : OnCtx Γ (env.IsType L.length))
    (h : env.IsDefEq L.length Γ e e' A) (hA : env.HasType L.length Γ A (.sort u)) :
    termClass env Γ L e = termClass env Γ L e' := by
  apply congrArg classLevel
  exact propext (IsProofTerm.congr henv hΓ h hA)

/-- Semantic values assigned to constants at evaluated universe arguments. -/
structure Assignment where
  constVal : Name → List Nat → ZFSet.{u}

/-- The empty/default assignment used when no constants are present. -/
noncomputable def Assignment.empty : Assignment.{u} where
  constVal _ _ := ∅

/-- Total structural interpretation of raw expressions. Soundness constrains it only on typed
expressions and modeled context valuations. -/
noncomputable def interp (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) : VExpr → ZFSet.{u}
  | .bvar i => γ.getD i bullet
  | .sort l => interpLevel κ L l
  | .const c ls =>
      if safeTermClass env Γ L (.const c ls) = 0 then bullet
      else assignment.constVal c (ls.map (VLevel.eval L))
  | .app f a =>
      appValue (safeTermClass env Γ L f)
        (interp κ env assignment L Γ γ f) (interp κ env assignment L Γ γ a)
  | .lam A body =>
      lamValue (safeTermClass env (A :: Γ) L body)
        (interp κ env assignment L Γ γ A)
        (fun x => interp κ env assignment L (A :: Γ) (x :: γ) body)
  | .forallE A body =>
      piValue (safeTypeClass env (A :: Γ) L body)
        (interp κ env assignment L Γ γ A)
        (fun x => interp κ env assignment L (A :: Γ) (x :: γ) body)

@[simp]
theorem interp_bvar (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (i : Nat) :
    interp κ env assignment L Γ γ (.bvar i) = γ.getD i bullet := rfl

@[simp]
theorem interp_sort (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (l : VLevel) :
    interp κ env assignment L Γ γ (.sort l) = interpLevel κ L l := rfl

@[simp]
theorem interp_const (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (c : Name) (ls : List VLevel) :
    interp κ env assignment L Γ γ (.const c ls) =
      if safeTermClass env Γ L (.const c ls) = 0 then bullet
      else assignment.constVal c (ls.map (VLevel.eval L)) := rfl

@[simp]
theorem interp_app (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (f a : VExpr) :
    interp κ env assignment L Γ γ (.app f a) =
      appValue (safeTermClass env Γ L f)
        (interp κ env assignment L Γ γ f) (interp κ env assignment L Γ γ a) := rfl

@[simp]
theorem interp_lam (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (A body : VExpr) :
    interp κ env assignment L Γ γ (.lam A body) =
      lamValue (safeTermClass env (A :: Γ) L body)
        (interp κ env assignment L Γ γ A)
        (fun x => interp κ env assignment L (A :: Γ) (x :: γ) body) := rfl

@[simp]
theorem interp_forallE (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (A body : VExpr) :
    interp κ env assignment L Γ γ (.forallE A body) =
      piValue (safeTypeClass env (A :: Γ) L body)
        (interp κ env assignment L Γ γ A)
        (fun x => interp κ env assignment L (A :: Γ) (x :: γ) body) := rfl

section SanityChecks

variable (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
  (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u})

example : interp κ env assignment L Γ γ (.sort .zero) = propUniverse := by
  rfl

example (A body : VExpr) :
    interp κ env assignment L Γ γ (.forallE A body) =
      piValue (safeTypeClass env (A :: Γ) L body)
        (interp κ env assignment L Γ γ A)
        (fun x => interp κ env assignment L (A :: Γ) (x :: γ) body) := by
  rfl

end SanityChecks

end Lean4LeanModel
