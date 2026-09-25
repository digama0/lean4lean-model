import Lean4LeanModel.QuotientModel

namespace Lean4LeanModel
open Lean4Lean
universe u

/-- The proof-irrelevant induction value inhabits lean4lean's exact generated `Quot.ind` type. -/
theorem quotIndConstValue_valid {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}}
    (henv : env.WF) (hQuotDecl : env.constants ``Quot = some quotConst)
    (hMkDecl : env.constants ``Quot.mk = some quotMkConst)
    (hQuot : assignment.ModelsQuot κ) (n : Nat) :
    quotIndConstValue ∈ interp κ env assignment [n] [] [] quotIndConst.type := by
  let α : VExpr := .sort (.param 0)
  let rel : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
  let q : VExpr := ((VExpr.const ``Quot [.param 0]).app (.bvar 1)).app (.bvar 0)
  let pred : VExpr := .forallE q (.sort .zero)
  let mk : VExpr := (((VExpr.const ``Quot.mk [.param 0]).app (.bvar 3)).app
    (.bvar 2)).app (.bvar 0)
  let premise : VExpr := .forallE (VExpr.bvar 2) ((VExpr.bvar 1).app mk)
  let result : VExpr := .forallE
    (((VExpr.const ``Quot [.param 0]).app (.bvar 3)).app (.bvar 2))
    ((VExpr.bvar 2).app (.bvar 0))
  let bodyP : VExpr := .forallE premise result
  let bodyR : VExpr := .forallE pred bodyP
  let bodyA : VExpr := .forallE rel bodyR
  let Γα := [α]
  let Γr := [rel, α]
  let Γp := [pred, rel, α]
  let Γc := [premise, pred, rel, α]
  let q' : VExpr := ((VExpr.const ``Quot [.param 0]).app (.bvar 3)).app (.bvar 2)
  let Γq := [q', premise, pred, rel, α]
  have hα : env.IsType 1 [] α := ⟨?_, by simp only [α]; type_tac⟩
  have hΓα : OnCtx Γα (env.IsType 1) := ⟨trivial, hα⟩
  have hrel : env.IsType 1 Γα rel := ⟨?_, by simp only [Γα, rel, α]; type_tac⟩
  have hΓr : OnCtx Γr (env.IsType 1) := ⟨hΓα, hrel⟩
  have hpred : env.IsType 1 Γr pred :=
    ⟨?_, by simp only [Γr, pred, q, rel, α]; type_tac⟩
  have hΓp : OnCtx Γp (env.IsType 1) := ⟨hΓr, hpred⟩
  have hpremise : env.IsType 1 Γp premise :=
    ⟨?_, by simp only [Γp, premise, mk, pred, q, rel, α]; type_tac⟩
  have hΓc : OnCtx Γc (env.IsType 1) := ⟨hΓp, hpremise⟩
  have hq' : env.IsType 1 Γc q' :=
    ⟨?_, by simp only [Γc, q', premise, mk, pred, q, rel, α]; type_tac⟩
  have hΓq : OnCtx Γq (env.IsType 1) := ⟨hΓc, hq'⟩
  have hpq : env.HasType 1 Γq ((VExpr.bvar 2).app (.bvar 0)) (.sort .zero) := by
    simp only [Γq, q', premise, mk, pred, q, rel, α]
    type_tac
  have hcPq : safeTypeClass env Γq [n] ((VExpr.bvar 2).app (.bvar 0)) = 0 :=
    safeTypeClass_eq_zero_of_hasType henv hΓq hpq
  have hresult : env.IsType 1 Γc result :=
    ⟨?_, by simp only [Γc, result, premise, mk, pred, q, rel, α]; type_tac⟩
  have hcResult : safeTypeClass env Γc [n] result = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := Γc) henv hΓc hq' ⟨.zero, hpq⟩]
    exact hcPq
  have hbodyP : env.IsType 1 Γp bodyP :=
    ⟨?_, by simp only [Γp, bodyP, result, premise, mk, pred, q, rel, α]; type_tac⟩
  have hcBodyP : safeTypeClass env Γp [n] bodyP = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := Γp) henv hΓp hpremise hresult]
    exact hcResult
  have hbodyR : env.IsType 1 Γr bodyR :=
    ⟨?_, by simp only [Γr, bodyR, bodyP, result, premise, mk, pred, q, rel, α]; type_tac⟩
  have hcBodyR : safeTypeClass env Γr [n] bodyR = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := Γr) henv hΓr hpred hbodyP]
    exact hcBodyP
  have hbodyA : env.IsType 1 Γα bodyA :=
    ⟨?_, by simp only [Γα, bodyA, bodyR, bodyP, result, premise, mk, pred, q, rel, α]; type_tac⟩
  have hcBodyA : safeTypeClass env Γα [n] bodyA = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := Γα) henv hΓα hrel hbodyR]
    exact hcBodyR
  let qc : VExpr := .const ``Quot [.param 0]
  let lrel : VLevel := .imax (.param 0) (.imax (.param 0) (.succ .zero))
  let lqA : VLevel := .imax lrel (.succ (.param 0))
  let lqc : VLevel := .imax (.succ (.param 0)) lqA
  have hcQcR : safeTermClass env Γr [n] qc ≠ 0 := by
    apply safeTermClass_ne_zero_of_hasType (l := lqc) henv hΓr
    · exact VEnv.HasType.const (U := 1) hQuotDecl (by decide) (by decide)
    · simpa [qc, quotConst, VExpr.instL, VLevel.inst] using (show env.HasType 1 Γr
        (.forallE (.sort (.param 0))
          (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
            (.sort (.param 0)))) (.sort lqc) from by
          simp only [lqc, lqA, lrel]
          apply VEnv.HasType.forallE
          · exact .sort (by decide)
          · apply VEnv.HasType.forallE
            · apply VEnv.HasType.forallE
              · type_tac
              · apply VEnv.HasType.forallE
                · type_tac
                · exact .sort trivial
            · exact .sort (by decide))
    · simp [lqc, lqA, lrel, VLevel.eval, Nat.imax]
  let relA : VExpr := .forallE (.bvar 1) (.forallE (.bvar 2) (.sort .zero))
  let qAType : VExpr := .forallE relA (.sort (.param 0))
  let qA : VExpr := qc.app (.bvar 1)
  have hqA : env.HasType 1 Γr qA qAType := by
    simp only [Γr, qA, qAType, relA, qc, rel, α]
    type_tac
  have hqATy : env.HasType 1 Γr qAType (.sort lqA) := by
    simp only [qAType, relA, lqA, lrel]
    apply VEnv.HasType.forallE
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.forallE
        · type_tac
        · exact .sort trivial
    · exact .sort (by decide)
  have hcQAR : safeTermClass env Γr [n] qA ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓr hqA hqATy (by simp [lqA, lrel, VLevel.eval, Nat.imax])
  have hqInterp (A r : ZFSet.{u}) (hA : A ∈ ModelUniverse κ n)
      (hr : r ∈ relationSpace A) :
      interp κ env assignment [n] [rel, α] [r, A] q =
        quotValue n A (relationOfGraph r) := by
    simp only [q, interp_app, interp_const, interp_bvar]
    have hcQcR' := hcQcR
    have hcQAR' := hcQAR
    simp only [Γr, qc, qA] at hcQcR' hcQAR'
    simp only [hcQcR', hcQAR', if_false, appValue, List.map, VLevel.eval,
      List.getD_cons_zero, List.getD_cons_succ, hQuot.1, quotTypeValue]
    rw [depApp_depLam hA, depApp_depLam hr]
  have hΓrelA : OnCtx [.bvar 0, α] (env.IsType 1) :=
    ⟨hΓα, ⟨.param 0, by simp only [α]; type_tac⟩⟩
  have hΓrelAB : OnCtx [.bvar 1, .bvar 0, α] (env.IsType 1) :=
    ⟨hΓrelA, ⟨.param 0, by simp only [α]; type_tac⟩⟩
  have hcRelInner :
      safeTypeClass env [.bvar 1, .bvar 0, α] [n] (.sort .zero) ≠ 0 :=
    safeTypeClass_sort_ne_zero henv hΓrelAB .zero trivial
  have hcRelOuter : safeTypeClass env [.bvar 0, α] [n]
      (.forallE (.bvar 1) (.sort .zero)) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n]) (Γ := [.bvar 0, α]) henv hΓrelA
      (show env.IsType 1 [.bvar 0, α] (.bvar 1) from ⟨.param 0, by type_tac⟩)
      (show env.IsType 1 [.bvar 1, .bvar 0, α] (.sort .zero) from
        ⟨.succ .zero, .sort trivial⟩)]
    exact hcRelInner
  have hrelation (A : ZFSet.{u}) :
      interp κ env assignment [n] [α] [A] rel = relationSpace A := by
    simp only [rel, interp_forallE, interp_sort, interpLevel, VLevel.eval,
      List.getD_cons_zero, interp_bvar, ModelUniverse_zero]
    simp only [piValue, if_neg hcRelOuter, if_neg hcRelInner, relationSpace,
      List.getD_cons_succ]
    simp only [List.getD_cons_zero]
  have hΓpredQ : OnCtx [q, rel, α] (env.IsType 1) :=
    ⟨hΓr, ⟨.param 0, by simp only [q, rel, α]; type_tac⟩⟩
  have hcPredBody : safeTypeClass env [q, rel, α] [n] (.sort .zero) ≠ 0 :=
    safeTypeClass_sort_ne_zero henv hΓpredQ .zero trivial
  have hpredInterp (A r : ZFSet.{u}) (hA : A ∈ ModelUniverse κ n)
      (hr : r ∈ relationSpace A) :
      interp κ env assignment [n] [rel, α] [r, A] pred =
        quotPredicateSpace n A (relationOfGraph r) := by
    simp only [pred, interp_forallE, interp_sort, interpLevel, VLevel.eval]
    simp only [piValue, if_neg hcPredBody, ModelUniverse_zero, quotPredicateSpace]
    rw [hqInterp A r hA hr]
  have hcQcC : safeTermClass env Γc [n] qc ≠ 0 := by
    apply safeTermClass_ne_zero_of_hasType (l := lqc) henv hΓc
    · exact VEnv.HasType.const (U := 1) hQuotDecl (by decide) (by decide)
    · simpa [qc, quotConst, VExpr.instL, VLevel.inst] using (show env.HasType 1 Γc
        (.forallE (.sort (.param 0))
          (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
            (.sort (.param 0)))) (.sort lqc) from by
          simp only [lqc, lqA, lrel]
          apply VEnv.HasType.forallE
          · exact .sort (by decide)
          · apply VEnv.HasType.forallE
            · apply VEnv.HasType.forallE
              · type_tac
              · apply VEnv.HasType.forallE
                · type_tac
                · exact .sort trivial
            · exact .sort (by decide))
    · simp [lqc, lqA, lrel, VLevel.eval, Nat.imax]
  let relC : VExpr := .forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero))
  let qCType : VExpr := .forallE relC (.sort (.param 0))
  let qC : VExpr := qc.app (.bvar 3)
  have hqC : env.HasType 1 Γc qC qCType := by
    simp only [Γc, qC, qCType, relC, qc, premise, mk, pred, q, rel, α]
    type_tac
  have hqCTy : env.HasType 1 Γc qCType (.sort lqA) := by
    simp only [qCType, relC, lqA, lrel]
    apply VEnv.HasType.forallE
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.forallE
        · type_tac
        · exact .sort trivial
    · exact .sort (by decide)
  have hcQAC : safeTermClass env Γc [n] qC ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓc hqC hqCTy (by simp [lqA, lrel, VLevel.eval, Nat.imax])
  have hqInterpC (A r P c : ZFSet.{u}) (hA : A ∈ ModelUniverse κ n)
      (hr : r ∈ relationSpace A) :
      interp κ env assignment [n] [premise, pred, rel, α] [c, P, r, A] q' =
        quotValue n A (relationOfGraph r) := by
    simp only [q', interp_app, interp_const, interp_bvar]
    have hcQcC' := hcQcC
    have hcQAC' := hcQAC
    simp only [Γc, qc, qC] at hcQcC' hcQAC'
    simp only [hcQcC', hcQAC', if_false, appValue, List.map, VLevel.eval,
      List.getD_cons_zero, List.getD_cons_succ, hQuot.1, quotTypeValue]
    rw [depApp_depLam hA, depApp_depLam hr]
  let lpred : VLevel := .imax (.param 0) (.succ .zero)
  let predC : VExpr := .forallE
    (((VExpr.const ``Quot [.param 0]).app (.bvar 4)).app (.bvar 3)) (.sort .zero)
  have hPredVar : env.HasType 1 Γq (.bvar 2) predC := by
    simp only [Γq, predC, q', premise, mk, pred, q, rel, α]
    exact .bvar (by lookup_tac)
  have hPredCTy : env.HasType 1 Γq predC (.sort lpred) := by
    simp only [predC, lpred]
    exact .forallE (by
      simp only [Γq, q', premise, mk, pred, q, rel, α]
      type_tac) (.sort trivial)
  have hcPredVar : safeTermClass env Γq [n] (.bvar 2) ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓq hPredVar hPredCTy (by simp [lpred, VLevel.eval, Nat.imax])
  have hpqInterp (A r P c qv : ZFSet.{u}) :
      interp κ env assignment [n] [q', premise, pred, rel, α]
        [qv, c, P, r, A] ((VExpr.bvar 2).app (.bvar 0)) = depApp P qv := by
    simp only [interp_app, interp_bvar]
    have hcPredVar' := hcPredVar
    simp only [Γq] at hcPredVar'
    simp only [hcPredVar', if_false, appValue, List.getD_cons_zero,
      List.getD_cons_succ]
  let Γa : List VExpr := [.bvar 2, pred, rel, α]
  have haTy : env.IsType 1 Γp (.bvar 2) :=
    ⟨.param 0, by simp only [Γp, pred, q, rel, α]; type_tac⟩
  have hΓa : OnCtx Γa (env.IsType 1) := ⟨hΓp, haTy⟩
  have hpMk : env.HasType 1 Γa ((VExpr.bvar 1).app mk) (.sort .zero) := by
    simp only [Γa, mk, pred, q, rel, α]
    type_tac
  have hcPMk : safeTypeClass env Γa [n] ((VExpr.bvar 1).app mk) = 0 :=
    safeTypeClass_eq_zero_of_hasType henv hΓa hpMk
  let predA : VExpr := .forallE
    (((VExpr.const ``Quot [.param 0]).app (.bvar 3)).app (.bvar 2)) (.sort .zero)
  have hPredVarA : env.HasType 1 Γa (.bvar 1) predA := by
    simp only [Γa, predA, pred, q, rel, α]
    exact .bvar (by lookup_tac)
  have hPredATy : env.HasType 1 Γa predA (.sort lpred) := by
    simp only [predA, lpred]
    exact .forallE (by
      simp only [Γa, pred, q, rel, α]
      type_tac) (.sort trivial)
  have hcPredVarA : safeTermClass env Γa [n] (.bvar 1) ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓa hPredVarA hPredATy (by simp [lpred, VLevel.eval, Nat.imax])
  let mkc : VExpr := .const ``Quot.mk [.param 0]
  let lmkR : VLevel := .imax (.param 0) (.param 0)
  let lmkA : VLevel := .imax lrel lmkR
  let lmkc : VLevel := .imax (.succ (.param 0)) lmkA
  have hmkc : env.HasType 1 Γa mkc quotMkConst.type :=
    VEnv.HasType.const (U := 1) hMkDecl (by decide) (by decide)
  have hmkcTy : env.HasType 1 Γa quotMkConst.type (.sort lmkc) := by
    simpa [quotMkConst, VExpr.instL, VLevel.inst] using (show env.HasType 1 Γa quotMkConst.type
        (.sort lmkc) from by
          simp only [quotMkConst, lmkc, lmkA, lmkR, lrel]
          apply VEnv.HasType.forallE
          · exact .sort (by decide)
          · apply VEnv.HasType.forallE
            · apply VEnv.HasType.forallE
              · type_tac
              · apply VEnv.HasType.forallE
                · type_tac
                · exact .sort trivial
            · apply VEnv.HasType.forallE
              · type_tac
              · apply VEnv.HasType.app'
                · type_tac
                · type_tac
                · rfl)
  have hcMkc : safeTermClass env Γa [n] mkc = 0 ↔ n = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n]) henv hΓa hmkc hmkcTy]
    simp [lmkc, lmkA, lmkR, lrel, VLevel.eval, Nat.imax]
  let mkA : VExpr := mkc.app (.bvar 3)
  let mkAType : VExpr := .forallE
    (.forallE (.bvar 3) (.forallE (.bvar 4) (.sort .zero)))
    (.forallE (.bvar 4)
      (((VExpr.const ``Quot [.param 0]).app (.bvar 5)).app (.bvar 1)))
  have hmkA : env.HasType 1 Γa mkA mkAType := by
    simp only [Γa, mkA, mkAType, mkc, pred, q, rel, α]
    type_tac
  have hmkATy : env.HasType 1 Γa mkAType (.sort lmkA) := by
    simp only [mkAType, lmkA, lmkR, lrel]
    apply VEnv.HasType.forallE
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.forallE
        · type_tac
        · exact .sort trivial
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.app'
        · type_tac
        · type_tac
        · rfl
  have hcMkA : safeTermClass env Γa [n] mkA = 0 ↔ n = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n]) henv hΓa hmkA hmkATy]
    simp [lmkA, lmkR, lrel, VLevel.eval, Nat.imax]
  let mkR : VExpr := mkA.app (.bvar 2)
  let mkRType : VExpr := .forallE (.bvar 3)
    (((VExpr.const ``Quot [.param 0]).app (.bvar 4)).app (.bvar 3))
  have hmkR : env.HasType 1 Γa mkR mkRType := by
    simp only [Γa, mkR, mkRType, mkA, mkc, pred, q, rel, α]
    type_tac
  have hmkRTy : env.HasType 1 Γa mkRType (.sort lmkR) := by
    simp only [mkRType, lmkR]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.app'
      · type_tac
      · type_tac
      · rfl
  have hcMkR : safeTermClass env Γa [n] mkR = 0 ↔ n = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n]) henv hΓa hmkR hmkRTy]
    simp [lmkR, VLevel.eval, Nat.imax]
  have hmkInterp (A r P a : ZFSet.{u}) (hA : A ∈ ModelUniverse κ n)
      (hr : r ∈ relationSpace A) (ha : a ∈ A) :
      interp κ env assignment [n] [.bvar 2, pred, rel, α] [a, P, r, A] mk =
        quotMkValue n A (relationOfGraph r) a := by
    simp only [mk, interp_app, interp_const, interp_bvar]
    have hcMkc' := hcMkc
    have hcMkA' := hcMkA
    have hcMkR' := hcMkR
    simp only [Γa, mkc, mkA, mkR] at hcMkc' hcMkA' hcMkR'
    cases n with
    | zero =>
      have h₀ := hcMkc'.2 rfl
      have h₁ := hcMkA'.2 rfl
      have h₂ := hcMkR'.2 rfl
      simp [h₂, quotMkValue, appValue]
    | succ n =>
      have h₀ : safeTermClass env [.bvar 2, pred, rel, α] [n + 1]
          (VExpr.const ``Quot.mk [.param 0]) ≠ 0 := fun h => Nat.succ_ne_zero n (hcMkc'.1 h)
      have h₁ : safeTermClass env [.bvar 2, pred, rel, α] [n + 1]
          ((VExpr.const ``Quot.mk [.param 0]).app (.bvar 3)) ≠ 0 :=
        fun h => Nat.succ_ne_zero n (hcMkA'.1 h)
      have h₂ : safeTermClass env [.bvar 2, pred, rel, α] [n + 1]
          (((VExpr.const ``Quot.mk [.param 0]).app (.bvar 3)).app (.bvar 2)) ≠ 0 :=
        fun h => Nat.succ_ne_zero n (hcMkR'.1 h)
      simp only [h₀, h₁, h₂, if_false, hQuot.2, quotMkConstValue,
        lamValue, appValue, VLevel.eval, List.map, List.getD_cons_zero,
        List.getD_cons_succ,
        Nat.succ_ne_zero]
      rw [depApp_depLam hA, depApp_depLam hr]
      change appValue (n + 1) (quotMkFunction (n + 1) A (relationOfGraph r)) a = _
      exact app_quotMkFunction ha
  have hpremInterp (A r P : ZFSet.{u}) (hA : A ∈ ModelUniverse κ n)
      (hr : r ∈ relationSpace A) :
      interp κ env assignment [n] [pred, rel, α] [P, r, A] premise =
        quotIndPremise n A (relationOfGraph r) (depApp P) := by
    simp only [premise, interp_forallE, interp_bvar]
    have hcPMk' := hcPMk
    simp only [Γa] at hcPMk'
    rw [show safeTypeClass env [.bvar 2, pred, rel, α] [n]
      ((VExpr.bvar 1).app mk) = 0 from hcPMk']
    simp only [piValue, if_true, quotIndPremise]
    apply forallValue_congr
    intro a ha
    simp only [interp_app, interp_bvar]
    have hcPredVarA' := hcPredVarA
    simp only [Γa] at hcPredVarA'
    simp only [hcPredVarA', if_false, appValue, List.getD_cons_zero,
      List.getD_cons_succ]
    rw [hmkInterp A r P a hA hr ha]
  change quotIndConstValue ∈ interp κ env assignment [n] [] [] (.forallE α bodyA)
  simp only [interp_forallE]
  rw [piValue_congr_zero (show safeTypeClass env [α] [n] bodyA = 0 ↔ 0 = 0 from
    iff_of_true (by simpa [Γα] using hcBodyA) rfl)]
  simp only [α, interp_sort, interpLevel, VLevel.eval, List.getD_cons_zero]
  simp only [bodyA, interp_forallE]
  simp_rw [piValue_congr_zero (show
    safeTypeClass env [rel, .sort (.param 0)] [n] bodyR = 0 ↔ 0 = 0 from
      iff_of_true (by simpa only [Γr, α] using hcBodyR) rfl)]
  simp only [bodyR, interp_forallE]
  simp_rw [piValue_congr_zero (show
    safeTypeClass env [pred, rel, .sort (.param 0)] [n] bodyP = 0 ↔ 0 = 0 from
      iff_of_true (by simpa only [Γp, α] using hcBodyP) rfl)]
  simp only [bodyP, interp_forallE]
  simp_rw [piValue_congr_zero (show
    safeTypeClass env [premise, pred, rel, .sort (.param 0)] [n] result = 0 ↔ 0 = 0 from
      iff_of_true (by simpa only [Γc, α] using hcResult) rfl)]
  simp only [result, interp_forallE]
  simp_rw [show
    safeTypeClass env
      [((VExpr.const ``Quot [.param 0]).app (.bvar 3)).app (.bvar 2),
        premise, pred, rel, .sort (.param 0)] [n]
      ((VExpr.bvar 2).app (.bvar 0)) = 0 by
      simpa only [Γq, q', α] using hcPq]
  simp only [piValue, if_true, quotIndConstValue]
  rw [bullet_mem_forallValue]
  intro A hA
  rw [hrelation A]
  rw [bullet_mem_forallValue]
  intro r hr
  rw [hpredInterp A r hA hr]
  rw [bullet_mem_forallValue]
  intro P hP
  rw [bullet_mem_forallValue]
  intro c hc
  rw [hpremInterp A r P hA hr] at hc
  have hcEq : c = bullet := eq_bullet_of_mem_prop
    (forallValue_mem_propUniverse A fun a =>
      depApp P (quotMkValue n A (relationOfGraph r) a)) hc
  subst c
  rw [hqInterpC A r P bullet hA hr]
  have hpqInterp' := hpqInterp A r P bullet
  simp only [q', α] at hpqInterp'
  simp_rw [hpqInterp']
  exact bullet_mem_quotInd_of_premise hc

end Lean4LeanModel
