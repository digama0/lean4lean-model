import Lean4LeanModel.Transport

/-! # Semantic context conversion -/

namespace Lean4LeanModel

open Lean4Lean

universe u

theorem IsPropType.defeqCtx {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    {L : List Nat} {A : VExpr} (henv : env.Ordered)
    (h : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    IsPropType env U Γ₁ L A ↔ IsPropType env U Γ₂ L A := by
  constructor
  · rintro ⟨u, hA, hu⟩
    exact ⟨u, hA.defeqDFC henv h, hu⟩
  · rintro ⟨u, hA, hu⟩
    exact ⟨u, hA.defeqDFC henv (h.symm henv), hu⟩

theorem IsProofTerm.defeqCtx {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    {L : List Nat} {e : VExpr} (henv : env.Ordered)
    (h : VEnv.IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    IsProofTerm env U Γ₁ L e ↔ IsProofTerm env U Γ₂ L e := by
  constructor
  · rintro ⟨A, he, hA⟩
    exact ⟨A, he.defeqDFC henv h, (IsPropType.defeqCtx henv h).1 hA⟩
  · rintro ⟨A, he, hA⟩
    exact ⟨A, he.defeqDFC henv (h.symm henv), (IsPropType.defeqCtx henv h).2 hA⟩

theorem safeTypeClass_defeqCtx {env : VEnv} {L : List Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    {A : VExpr} (henv : env.Ordered) (hΓ₀ : OnCtx Γ₀ (env.IsType L.length))
    (h : VEnv.IsDefEqCtx env L.length Γ₀ Γ₁ Γ₂) :
    safeTypeClass env Γ₁ L A = safeTypeClass env Γ₂ L A := by
  have hΓ₁ := h.isType' hΓ₀
  have hΓ₂ := (h.symm henv).isType' hΓ₀
  rw [safeTypeClass_eq hΓ₁, safeTypeClass_eq hΓ₂]
  unfold typeClass
  exact congrArg classLevel (propext (IsPropType.defeqCtx henv h))

theorem safeTermClass_defeqCtx {env : VEnv} {L : List Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    {e : VExpr} (henv : env.Ordered) (hΓ₀ : OnCtx Γ₀ (env.IsType L.length))
    (h : VEnv.IsDefEqCtx env L.length Γ₀ Γ₁ Γ₂) :
    safeTermClass env Γ₁ L e = safeTermClass env Γ₂ L e := by
  have hΓ₁ := h.isType' hΓ₀
  have hΓ₂ := (h.symm henv).isType' hΓ₀
  rw [safeTermClass_eq hΓ₁, safeTermClass_eq hΓ₂]
  unfold termClass
  exact congrArg classLevel (propext (IsProofTerm.defeqCtx henv h))

private theorem interp_eq_of_not_onCtx {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ₁ Γ₂ : List VExpr}
    (h₁ : ¬OnCtx Γ₁ (env.IsType L.length)) (h₂ : ¬OnCtx Γ₂ (env.IsType L.length))
    (γ : List ZFSet.{u}) (e : VExpr) :
    interp κ env assignment L Γ₁ γ e = interp κ env assignment L Γ₂ γ e := by
  induction e generalizing Γ₁ Γ₂ γ with
  | bvar => rfl
  | sort => rfl
  | const c ls => simp [interp_const, safeTermClass, h₁, h₂]
  | app f a ihf iha =>
    simp only [interp_app]
    simp [safeTermClass, h₁, h₂, ihf h₁ h₂, iha h₁ h₂]
  | lam A body ihA ihbody =>
    simp only [interp_lam]
    have h₁' : ¬OnCtx (A :: Γ₁) (env.IsType L.length) := fun h => h₁ h.1
    have h₂' : ¬OnCtx (A :: Γ₂) (env.IsType L.length) := fun h => h₂ h.1
    simp [safeTermClass, h₁', h₂', ihA h₁ h₂]
    apply lamValue_congr
    intro x _
    exact ihbody h₁' h₂' (x :: γ)
  | forallE A body ihA ihbody =>
    simp only [interp_forallE]
    have h₁' : ¬OnCtx (A :: Γ₁) (env.IsType L.length) := fun h => h₁ h.1
    have h₂' : ¬OnCtx (A :: Γ₂) (env.IsType L.length) := fun h => h₂ h.1
    simp [safeTypeClass, h₁', h₂', ihA h₁ h₂]
    apply depFuns_congr
    intro x _
    exact ihbody h₁' h₂' (x :: γ)

/-- Interpretation is invariant under definitional conversion of the local context. -/
theorem interp_defeqCtx {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (henv : env.Ordered) (hΓ₀ : OnCtx Γ₀ (env.IsType L.length))
    (h : VEnv.IsDefEqCtx env L.length Γ₀ Γ₁ Γ₂)
    (γ : List ZFSet.{u}) (e : VExpr) :
    interp κ env assignment L Γ₁ γ e = interp κ env assignment L Γ₂ γ e := by
  induction e generalizing Γ₀ Γ₁ Γ₂ γ with
  | bvar => rfl
  | sort => rfl
  | const c ls =>
    simp only [interp_const]
    rw [safeTermClass_defeqCtx henv hΓ₀ h]
  | app f a ihf iha =>
    simp only [interp_app]
    rw [safeTermClass_defeqCtx henv hΓ₀ h, ihf hΓ₀ h, iha hΓ₀ h]
  | lam A body ihA ihbody =>
    simp only [interp_lam]
    rw [ihA hΓ₀ h]
    by_cases hA : env.IsType L.length Γ₁ A
    · obtain ⟨u, hAu⟩ := hA
      have h' : VEnv.IsDefEqCtx env L.length Γ₀ (A :: Γ₁) (A :: Γ₂) := .succ h hAu
      rw [safeTermClass_defeqCtx henv hΓ₀ h']
      apply lamValue_congr
      intro x _
      exact ihbody hΓ₀ h' (x :: γ)
    · have hA₂ : ¬env.IsType L.length Γ₂ A := fun hA₂ =>
        hA (hA₂.defeqDFC henv (h.symm henv))
      have hΓ₁ := h.isType' hΓ₀
      have hΓ₂ := (h.symm henv).isType' hΓ₀
      have hn₁ : ¬OnCtx (A :: Γ₁) (env.IsType L.length) := fun q => hA q.2
      have hn₂ : ¬OnCtx (A :: Γ₂) (env.IsType L.length) := fun q => hA₂ q.2
      simp [safeTermClass, hn₁, hn₂]
      apply lamValue_congr
      intro x _
      exact interp_eq_of_not_onCtx hn₁ hn₂ _ _
  | forallE A body ihA ihbody =>
    simp only [interp_forallE]
    rw [ihA hΓ₀ h]
    by_cases hA : env.IsType L.length Γ₁ A
    · obtain ⟨u, hAu⟩ := hA
      have h' : VEnv.IsDefEqCtx env L.length Γ₀ (A :: Γ₁) (A :: Γ₂) := .succ h hAu
      rw [safeTypeClass_defeqCtx henv hΓ₀ h']
      apply piValue_congr
      intro x _
      exact ihbody hΓ₀ h' (x :: γ)
    · have hA₂ : ¬env.IsType L.length Γ₂ A := fun hA₂ =>
        hA (hA₂.defeqDFC henv (h.symm henv))
      have hn₁ : ¬OnCtx (A :: Γ₁) (env.IsType L.length) := fun q => hA q.2
      have hn₂ : ¬OnCtx (A :: Γ₂) (env.IsType L.length) := fun q => hA₂ q.2
      simp [safeTypeClass, hn₁, hn₂]
      apply depFuns_congr
      intro x _
      exact interp_eq_of_not_onCtx hn₁ hn₂ _ _

end Lean4LeanModel
