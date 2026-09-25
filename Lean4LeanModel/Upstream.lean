import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Audited upstream metatheory boundary

The model needs only the zero/nonzero consequence of unique typing. Keeping its derivation here
makes direct dependence on lean4lean's still-sorried structural typing theorems explicit.
-/

namespace Lean4LeanModel.Upstream

open Lean4Lean

theorem propSort_eval_eq {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A : VExpr} {u v : VLevel} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hA' : env.HasType U Γ A (.sort v))
    (L : List Nat) : u.eval L = v.eval L := by
  obtain ⟨_, huv⟩ := hA.uniq henv hΓ hA'
  have huv' : u ≈ v := VEnv.IsDefEqU.sort_inv henv hΓ ⟨_, huv⟩
  exact VLevel.equiv_def.1 huv' L

theorem propSort_eval_zero_iff {env : VEnv} {U : Nat} {Γ : List VExpr}
    {A : VExpr} {u v : VLevel} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (hA : env.HasType U Γ A (.sort u)) (hA' : env.HasType U Γ A (.sort v))
    (L : List Nat) : u.eval L = 0 ↔ v.eval L = 0 := by
  rw [propSort_eval_eq henv hΓ hA hA' L]

/-- The universe levels of the result types of two typings of one term evaluate equally. -/
theorem termSort_eval_eq {env : VEnv} {U : Nat} {Γ : List VExpr}
    {e A B : VExpr} {u v : VLevel} (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    (heA : env.HasType U Γ e A) (hA : env.HasType U Γ A (.sort u))
    (heB : env.HasType U Γ e B) (hB : env.HasType U Γ B (.sort v))
    (L : List Nat) : u.eval L = v.eval L := by
  obtain ⟨w, hAB⟩ := heA.uniq henv hΓ heB
  exact (propSort_eval_eq henv hΓ hA hAB.hasType.1 L).trans
    (propSort_eval_eq henv hΓ hAB.hasType.2 hB L)

/-! The following adapters isolate the strengthening theorem currently proved with `sorry`
upstream.  The model uses it only to show that its raw-syntax classifiers ignore weakening. -/

theorem ctx_of_liftN {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr}
    (henv : env.WF) (hΓ' : OnCtx Γ' (env.IsType U)) (W : Ctx.LiftN n k Γ Γ') :
    OnCtx Γ (env.IsType U) :=
  hΓ'.weakN_inv henv W

theorem hasType_liftN_sort_iff {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr}
    {e : VExpr} {u : VLevel} (henv : env.WF) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') :
    env.HasType U Γ' (e.liftN n k) (.sort u) ↔ env.HasType U Γ e (.sort u) := by
  simpa [VExpr.liftN] using (VEnv.HasType.weakN_iff henv hΓ' W (e := e) (A := .sort u))

theorem strengthen_liftN_typing {env : VEnv} {U n k : Nat} {Γ Γ' : List VExpr}
    {e A' : VExpr} (henv : env.WF) (hΓ' : OnCtx Γ' (env.IsType U))
    (W : Ctx.LiftN n k Γ Γ') (he : env.HasType U Γ' (e.liftN n k) A') :
    ∃ A, env.HasType U Γ e A ∧ env.HasType U Γ' (e.liftN n k) (A.liftN n k) := by
  obtain ⟨A, heA⟩ := (VEnv.IsDefEqU.weakN_iff henv hΓ' W).1 ⟨A', he⟩
  exact ⟨A, heA, heA.weakN henv W⟩

end Lean4LeanModel.Upstream
