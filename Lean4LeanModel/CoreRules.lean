import Lean4LeanModel.ModelSetup

/-!
# Semantic core typing rules

These lemmas are the compositional kernel of the fundamental theorem.  They state the semantic
content of the universe, product, abstraction, and application rules independently of weakening
and substitution transport.
-/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- Semantic validity of a typing judgment at one context valuation. -/
def Satisfies (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (e A : VExpr) : Prop :=
  interp κ env assignment L Γ γ e ∈ interp κ env assignment L Γ γ A

theorem satisfies_sort {κ : ℕ → Cardinal.{u}} {env : VEnv} {assignment : Assignment.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u}) (l : VLevel) :
    Satisfies κ env assignment L Γ γ (.sort l) (.sort (.succ l)) := by
  change interpLevel κ L l ∈ interpLevel κ L (.succ l)
  exact ModelUniverse_mem_succ hκ hi (l.eval L)

theorem satisfies_forallE {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {γ : List ZFSet.{u}} {A B : VExpr} {uLvl vLvl : VLevel}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hAty : env.HasType L.length Γ A (.sort uLvl))
    (hBty : env.HasType L.length (A :: Γ) B (.sort vLvl))
    (hA : Satisfies κ env assignment L Γ γ A (.sort uLvl))
    (hB : ∀ x ∈ interp κ env assignment L Γ γ A,
      Satisfies κ env assignment L (A :: Γ) (x :: γ) B (.sort vLvl)) :
    Satisfies κ env assignment L Γ γ (.forallE A B) (.sort (.imax uLvl vLvl)) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, ⟨uLvl, hAty⟩⟩
  simp only [Satisfies, interp_forallE, interp_sort, safeTypeClass_eq hΓA]
  change piValue (typeClass env (A :: Γ) L B)
      (interp κ env assignment L Γ γ A)
      (fun x => interp κ env assignment L (A :: Γ) (x :: γ) B) ∈
    interpLevel κ L (.imax uLvl vLvl)
  apply piValue_mem_ModelUniverse_of_zero_iff hκ hi
    (typeClass_eq_zero_iff_of_hasType henv hΓA hBty)
  · exact hA
  · intro x hx
    exact hB x hx

theorem satisfies_lam {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {γ : List ZFSet.{u}} {A B body : VExpr} {uLvl vLvl : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hAty : env.HasType L.length Γ A (.sort uLvl))
    (hbodyTy : env.HasType L.length (A :: Γ) body B)
    (hBty : env.HasType L.length (A :: Γ) B (.sort vLvl))
    (hbody : ∀ x ∈ interp κ env assignment L Γ γ A,
      Satisfies κ env assignment L (A :: Γ) (x :: γ) body B)
    (hB : ∀ x ∈ interp κ env assignment L Γ γ A,
      Satisfies κ env assignment L (A :: Γ) (x :: γ) B (.sort vLvl)) :
    Satisfies κ env assignment L Γ γ (.lam A body) (.forallE A B) := by
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, ⟨uLvl, hAty⟩⟩
  have hclass : termClass env (A :: Γ) L body = typeClass env (A :: Γ) L B :=
    termClass_eq_typeClass_of_hasType henv hΓA hbodyTy hBty
  simp only [Satisfies, interp_lam, interp_forallE, safeTermClass_eq hΓA,
    safeTypeClass_eq hΓA]
  change lamValue (termClass env (A :: Γ) L body)
      (interp κ env assignment L Γ γ A)
      (fun x => interp κ env assignment L (A :: Γ) (x :: γ) body) ∈
    piValue (typeClass env (A :: Γ) L B)
      (interp κ env assignment L Γ γ A)
      (fun x => interp κ env assignment L (A :: Γ) (x :: γ) B)
  rw [hclass]
  apply lamValue_mem_piValue
  · exact hbody
  · intro hzero x hx
    have hv : vLvl.eval L = 0 :=
      (typeClass_eq_zero_iff_of_hasType henv hΓA hBty).1 hzero
    change interp κ env assignment L (A :: Γ) (x :: γ) B ∈ propUniverse
    simpa [Satisfies, interpLevel, hv] using hB x hx

/-- Application soundness before rewriting semantic substitution in the codomain. -/
theorem satisfies_app_fiber {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {γ : List ZFSet.{u}} {f a A B : VExpr} {uLvl vLvl : VLevel}
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hAty : env.HasType L.length Γ A (.sort uLvl))
    (hBty : env.HasType L.length (A :: Γ) B (.sort vLvl))
    (hfty : env.HasType L.length Γ f (.forallE A B))
    (hf : Satisfies κ env assignment L Γ γ f (.forallE A B))
    (ha : Satisfies κ env assignment L Γ γ a A) :
    interp κ env assignment L Γ γ (.app f a) ∈
      interp κ env assignment L (A :: Γ)
        (interp κ env assignment L Γ γ a :: γ) B := by
  have hAB : env.HasType L.length Γ (.forallE A B) (.sort (.imax uLvl vLvl)) :=
    .forallEDF hAty hBty
  have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, ⟨uLvl, hAty⟩⟩
  have hf' : interp κ env assignment L Γ γ f ∈
      piValue (typeClass env (A :: Γ) L B)
        (interp κ env assignment L Γ γ A)
        (fun x => interp κ env assignment L (A :: Γ) (x :: γ) B) := by
    simpa only [Satisfies, interp_forallE, safeTypeClass_eq hΓA] using hf
  have hclass : termClass env Γ L f = typeClass env (A :: Γ) L B := by
    calc
      termClass env Γ L f = typeClass env Γ L (.forallE A B) :=
        termClass_eq_typeClass_of_hasType henv hΓ hfty hAB
      _ = typeClass env (A :: Γ) L B := typeClass_forallE henv hΓ hAty hBty
  rw [interp_app, safeTermClass_eq hΓ]
  change appValue (termClass env Γ L f)
      (interp κ env assignment L Γ γ f) (interp κ env assignment L Γ γ a) ∈
    interp κ env assignment L (A :: Γ) (interp κ env assignment L Γ γ a :: γ) B
  rw [hclass]
  exact appValue_mem hf' ha

/-- The environment-independent false proposition denotes the empty truth value. -/
theorem interp_false_eq_empty (κ : ℕ → Cardinal.{u}) (env : VEnv)
    (assignment : Assignment.{u}) (L : List Nat) :
    interp κ env assignment L [] [] VExpr.false = (∅ : ZFSet.{u}) := by
  have hclass : typeClass env [.sort .zero] L (.bvar 0) = 0 := by
    rw [typeClass_eq_zero]
    exact ⟨.zero, .bvar .zero, rfl⟩
  have hctx : OnCtx [.sort .zero] (env.IsType L.length) := by
    refine ⟨trivial, .succ .zero, ?_⟩
    exact .sortDF (by trivial) (by trivial) rfl
  rw [show VExpr.false = .forallE (.sort .zero) (.bvar 0) from rfl, interp_forallE]
  simp only [interp_sort, safeTypeClass_eq hctx, hclass, piValue, if_pos]
  rw [forallValue]
  apply truthValue_of_neg
  intro h
  have hempty : (∅ : ZFSet.{u}) ∈ propUniverse := by
    simp [propUniverse, bullet]
  have := h ∅ hempty
  simpa [bullet] using this

end Lean4LeanModel
