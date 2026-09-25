import Lean4LeanModel.QuotientIndModel

namespace Lean4LeanModel
open Lean4Lean
universe u

set_option maxHeartbeats 350000

private theorem quotLiftConstValue_mem_of_domains {κ : ℕ → Cardinal.{u}}
    {n m : Nat}
    {respectDomain : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u}}
    {quotDomain : ZFSet.{u} → ZFSet.{u} → ZFSet.{u} → ZFSet.{u} →
      ZFSet.{u} → ZFSet.{u}}
    (hrespect : ∀ A ∈ ModelUniverse κ n, ∀ r ∈ relationSpace A,
      ∀ B ∈ ModelUniverse κ m, ∀ f ∈ piValue m A (fun _ => B),
        respectDomain A r B f =
          truthValue (QuotientRespects m A (relationOfGraph r) f))
    (hquot : ∀ A ∈ ModelUniverse κ n, ∀ r ∈ relationSpace A,
      ∀ B ∈ ModelUniverse κ m, ∀ f ∈ piValue m A (fun _ => B),
      ∀ c ∈ respectDomain A r B f,
        quotDomain A r B f c = quotValue n A (relationOfGraph r)) :
    quotLiftConstValue κ n m ∈ piValue m (ModelUniverse κ n) (fun A =>
      piValue m (relationSpace A) (fun r =>
        piValue m (ModelUniverse κ m) (fun B =>
          piValue m (piValue m A (fun _ => B)) (fun f =>
            piValue m (respectDomain A r B f) (fun c =>
              piValue m (quotDomain A r B f c) (fun _ => B)))))) := by
  have hspace :
      piValue m (ModelUniverse κ n) (fun A =>
        piValue m (relationSpace A) (fun r =>
          piValue m (ModelUniverse κ m) (fun B =>
            piValue m (piValue m A (fun _ => B)) (fun f =>
              piValue m (respectDomain A r B f) (fun c =>
                piValue m (quotDomain A r B f c) (fun _ => B)))))) =
      piValue m (ModelUniverse κ n) (fun A =>
        piValue m (relationSpace A) (fun r =>
          piValue m (ModelUniverse κ m) (fun B =>
            piValue m (piValue m A (fun _ => B)) (fun f =>
              piValue m (truthValue (QuotientRespects m A (relationOfGraph r) f))
                (fun _ => piValue m (quotValue n A (relationOfGraph r)) (fun _ => B)))))) := by
    apply piValue_congr
    intro A hA
    apply piValue_congr
    intro r hr
    apply piValue_congr
    intro B hB
    apply piValue_congr
    intro f hf
    have hR := hrespect A hA r hr B hB f hf
    rw [hR]
    apply piValue_congr
    intro c hc
    rw [hquot A hA r hr B hB f hf c (by rw [hR]; exact hc)]
  rw [hspace]
  exact quotLiftConstValue_mem n m

/-- The constructed lift inhabits lean4lean's exact generated `Quot.lift` type. -/
theorem quotLiftConstValue_valid {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}}
    (henv : env.WF) (hEqDecl : env.constants ``Eq = some eqConst)
    (hQuotDecl : env.constants ``Quot = some quotConst)
    (hEq : assignment.ModelsEq κ)
    (hQuot : ∀ n, assignment.constVal ``Quot [n] = quotTypeValue κ n)
    (n m : Nat) :
    quotLiftConstValue κ n m ∈
      interp κ env assignment [n, m] [] [] quotLiftConst.type := by
  let α : VExpr := .sort (.param 0)
  let rel : VExpr := .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))
  let β : VExpr := .sort (.param 1)
  let fn : VExpr := .forallE (.bvar 2) (.bvar 1)
  let eqApp : VExpr :=
    (((VExpr.const ``Eq [.param 1]).app (.bvar 4)).app
      ((VExpr.bvar 3).app (.bvar 2))).app ((VExpr.bvar 3).app (.bvar 1))
  let rab : VExpr := ((VExpr.bvar 4).app (.bvar 1)).app (.bvar 0)
  let respect : VExpr := .forallE (.bvar 3) <| .forallE (.bvar 4) <|
    .forallE rab eqApp
  let quot : VExpr := ((VExpr.const ``Quot [.param 0]).app (.bvar 4)).app (.bvar 3)
  let result : VExpr := .forallE quot (.bvar 3)
  let bodyC : VExpr := .forallE respect result
  let bodyF : VExpr := .forallE fn bodyC
  let bodyB : VExpr := .forallE β bodyF
  let bodyR : VExpr := .forallE rel bodyB
  let Γα := [α]
  let Γr := [rel, α]
  let Γβ := [β, rel, α]
  let Γf := [fn, β, rel, α]
  let Γc := [respect, fn, β, rel, α]
  let Γq := [quot, respect, fn, β, rel, α]
  have hα : env.IsType 2 [] α := ⟨?_, by simp only [α]; type_tac⟩
  have hΓα : OnCtx Γα (env.IsType 2) := ⟨trivial, hα⟩
  have hrel : env.IsType 2 Γα rel := ⟨?_, by simp only [Γα, rel, α]; type_tac⟩
  have hΓr : OnCtx Γr (env.IsType 2) := ⟨hΓα, hrel⟩
  have hβ : env.IsType 2 Γr β := ⟨?_, by simp only [Γr, β, rel, α]; type_tac⟩
  have hΓβ : OnCtx Γβ (env.IsType 2) := ⟨hΓr, hβ⟩
  have hfn : env.IsType 2 Γβ fn := ⟨?_, by simp only [Γβ, fn, β, rel, α]; type_tac⟩
  have hΓf : OnCtx Γf (env.IsType 2) := ⟨hΓβ, hfn⟩
  have hrespect : env.IsType 2 Γf respect :=
    ⟨?_, by simp only [Γf, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hΓc : OnCtx Γc (env.IsType 2) := ⟨hΓf, hrespect⟩
  have hquot : env.IsType 2 Γc quot :=
    ⟨?_, by simp only [Γc, quot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hΓq : OnCtx Γq (env.IsType 2) := ⟨hΓc, hquot⟩
  have hresHT : env.HasType 2 Γq (.bvar 3) (.sort (.param 1)) := by
    simp only [Γq, quot, respect, eqApp, rab, fn, β, rel, α]
    type_tac
  have hres : env.IsType 2 Γq (.bvar 3) := ⟨.param 1, hresHT⟩
  have hcRes : safeTypeClass env Γq [n, m] (.bvar 3) = 0 ↔ m = 0 := by
    rw [safeTypeClass_eq hΓq,
      typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓq hresHT]
    simp [VLevel.eval]
  have hresult : env.IsType 2 Γc result :=
    ⟨?_, by simp only [Γc, result, quot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hcResult : safeTypeClass env Γc [n, m] result = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γc) henv hΓc hquot hres]
    exact hcRes
  have hbodyC : env.IsType 2 Γf bodyC :=
    ⟨?_, by simp only [Γf, bodyC, result, quot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hcBodyC : safeTypeClass env Γf [n, m] bodyC = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γf) henv hΓf hrespect hresult]
    exact hcResult
  have hbodyF : env.IsType 2 Γβ bodyF :=
    ⟨?_, by simp only [Γβ, bodyF, bodyC, result, quot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hcBodyF : safeTypeClass env Γβ [n, m] bodyF = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γβ) henv hΓβ hfn hbodyC]
    exact hcBodyC
  have hbodyB : env.IsType 2 Γr bodyB :=
    ⟨?_, by simp only [Γr, bodyB, bodyF, bodyC, result, quot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hcBodyB : safeTypeClass env Γr [n, m] bodyB = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γr) henv hΓr hβ hbodyF]
    exact hcBodyF
  have hbodyR : env.IsType 2 Γα bodyR :=
    ⟨?_, by simp only [Γα, bodyR, bodyB, bodyF, bodyC, result, quot, respect, eqApp, rab, fn, β, rel, α]; type_tac⟩
  have hcBodyR : safeTypeClass env Γα [n, m] bodyR = 0 ↔ m = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γα) henv hΓα hrel hbodyB]
    exact hcBodyB
  have hΓrelA : OnCtx [.bvar 0, α] (env.IsType 2) :=
    ⟨hΓα, ⟨.param 0, by simp only [α]; type_tac⟩⟩
  have hΓrelAB : OnCtx [.bvar 1, .bvar 0, α] (env.IsType 2) :=
    ⟨hΓrelA, ⟨.param 0, by simp only [α]; type_tac⟩⟩
  have hcRelInner : safeTypeClass env [.bvar 1, .bvar 0, α]
      [n, m] (.sort .zero) ≠ 0 := safeTypeClass_sort_ne_zero henv hΓrelAB .zero trivial
  have hcRelOuter : safeTypeClass env [.bvar 0, α] [n, m]
      (.forallE (.bvar 1) (.sort .zero)) ≠ 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := [.bvar 0, α]) henv hΓrelA
      (show env.IsType 2 [.bvar 0, α] (.bvar 1) from ⟨.param 0, by type_tac⟩)
      (show env.IsType 2 [.bvar 1, .bvar 0, α] (.sort .zero) from
        ⟨.succ .zero, .sort trivial⟩)]
    exact hcRelInner
  have hrelation (A : ZFSet.{u}) :
      interp κ env assignment [n, m] [α] [A] rel = relationSpace A := by
    simp only [rel, interp_forallE, interp_sort, interpLevel, VLevel.eval,
      List.getD_cons_zero, interp_bvar, ModelUniverse_zero]
    simp only [piValue, if_neg hcRelOuter, if_neg hcRelInner, relationSpace,
      List.getD_cons_succ]
    simp only [List.getD_cons_zero]
  have hΓfnA : OnCtx [.bvar 2, β, rel, α] (env.IsType 2) :=
    ⟨hΓβ, ⟨.param 0, by simp only [β, rel, α]; type_tac⟩⟩
  have hfnCodHT : env.HasType 2 [.bvar 2, β, rel, α] (.bvar 1)
      (.sort (.param 1)) := by simp only [β, rel, α]; type_tac
  have hcFnCod : safeTypeClass env [.bvar 2, β, rel, α]
      [n, m] (.bvar 1) = 0 ↔ m = 0 := by
    rw [safeTypeClass_eq hΓfnA,
      typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓfnA hfnCodHT]
    simp [VLevel.eval]
  let qc : VExpr := .const ``Quot [.param 0]
  let relC : VExpr := .forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))
  let qCType : VExpr := .forallE relC (.sort (.param 0))
  let qC : VExpr := qc.app (.bvar 4)
  let lrel : VLevel := .imax (.param 0) (.imax (.param 0) (.succ .zero))
  let lqC : VLevel := .imax lrel (.succ (.param 0))
  let lqc : VLevel := .imax (.succ (.param 0)) lqC
  have hqc : env.HasType 2 Γc qc (quotConst.type.instL [.param 0]) :=
    VEnv.HasType.const (U := 2) hQuotDecl (by decide) (by decide)
  have hqcTy : env.HasType 2 Γc (quotConst.type.instL [.param 0]) (.sort lqc) := by
    simpa [quotConst, VExpr.instL, VLevel.inst] using (show env.HasType 2 Γc
      (.forallE (.sort (.param 0))
        (.forallE (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)))
          (.sort (.param 0)))) (.sort lqc) from by
        simp only [lqc, lqC, lrel]
        apply VEnv.HasType.forallE
        · exact .sort (by decide)
        · apply VEnv.HasType.forallE
          · apply VEnv.HasType.forallE
            · type_tac
            · apply VEnv.HasType.forallE
              · type_tac
              · exact .sort trivial
          · exact .sort (by decide))
  have hcQc : safeTermClass env Γc [n, m] qc ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓc hqc hqcTy
      (by simp [lqc, lqC, lrel, VLevel.eval, Nat.imax])
  have hqC : env.HasType 2 Γc qC qCType := by
    simp only [Γc, qC, qCType, relC, qc, respect, eqApp, rab, fn, β, rel, α]
    type_tac
  have hqCTy : env.HasType 2 Γc qCType (.sort lqC) := by
    simp only [qCType, relC, lqC, lrel]
    apply VEnv.HasType.forallE
    · apply VEnv.HasType.forallE
      · type_tac
      · apply VEnv.HasType.forallE
        · type_tac
        · exact .sort trivial
    · exact .sort (by decide)
  have hcQC : safeTermClass env Γc [n, m] qC ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓc hqC hqCTy
      (by simp [lqC, lrel, VLevel.eval, Nat.imax])
  have hquotInterp (A r B f c : ZFSet.{u})
      (hA : A ∈ ModelUniverse κ n) (hr : r ∈ relationSpace A) :
      interp κ env assignment [n, m] [respect, fn, β, rel, α]
        [c, f, B, r, A] quot = quotValue n A (relationOfGraph r) := by
    simp only [quot, interp_app, interp_const, interp_bvar]
    have hcQc' := hcQc
    have hcQC' := hcQC
    simp only [Γc, qc, qC] at hcQc' hcQC'
    simp only [hcQc', hcQC', if_false, appValue, List.map, VLevel.eval,
      List.getD_cons_zero, List.getD_cons_succ, hQuot, quotTypeValue]
    rw [depApp_depLam hA, depApp_depLam hr]
  let Γa := [.bvar 3, fn, β, rel, α]
  let Γb := [.bvar 4, .bvar 3, fn, β, rel, α]
  let Γh := [rab, .bvar 4, .bvar 3, fn, β, rel, α]
  have haTy : env.IsType 2 Γf (.bvar 3) :=
    ⟨.param 0, by simp only [Γf, fn, β, rel, α]; type_tac⟩
  have hΓa : OnCtx Γa (env.IsType 2) := ⟨hΓf, haTy⟩
  have hbHT : env.HasType 2 Γa (.bvar 4) (.sort (.param 0)) := by
    simp only [Γa, fn, β, rel, α]; type_tac
  have hbTy : env.IsType 2 Γa (.bvar 4) := ⟨.param 0, hbHT⟩
  have hΓb : OnCtx Γb (env.IsType 2) := ⟨hΓa, hbTy⟩
  have hrabHT : env.HasType 2 Γb rab (.sort .zero) := by
    simp only [Γb, rab, fn, β, rel, α]; type_tac
  have hrabTy : env.IsType 2 Γb rab := ⟨.zero, hrabHT⟩
  have hΓh : OnCtx Γh (env.IsType 2) := ⟨hΓb, hrabTy⟩
  have heqApp : env.HasType 2 Γh eqApp (.sort .zero) := by
    simp only [Γh, eqApp, rab, fn, β, rel, α]
    type_tac
  have hcEqApp : safeTypeClass env Γh [n, m] eqApp = 0 := by
    rw [safeTypeClass_eq hΓh]
    exact (typeClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓh heqApp).2 rfl
  let respectH : VExpr := .forallE rab eqApp
  let respectB : VExpr := .forallE (.bvar 4) respectH
  have hrespectHHT : env.HasType 2 Γb respectH
      (.sort (.imax .zero .zero)) := by
    simpa only [respectH] using VEnv.HasType.forallE hrabHT heqApp
  have hrespectH : env.IsType 2 Γb respectH := ⟨_, hrespectHHT⟩
  have hcRespectH : safeTypeClass env Γb [n, m] respectH = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γb) henv hΓb hrabTy ⟨.zero, heqApp⟩]
    exact hcEqApp
  have hrespectBHT : env.HasType 2 Γa respectB
      (.sort (.imax (.param 0) (.imax .zero .zero))) := by
    simpa only [respectB] using VEnv.HasType.forallE hbHT hrespectHHT
  have hrespectB : env.IsType 2 Γa respectB := ⟨_, hrespectBHT⟩
  have hcRespectB : safeTypeClass env Γa [n, m] respectB = 0 := by
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γa) henv hΓa hbTy hrespectH]
    exact hcRespectH
  have hcRespect : safeTypeClass env Γf [n, m] respect = 0 := by
    rw [show respect = .forallE (.bvar 3) respectB by
      simp only [respect, respectB, respectH]]
    rw [safeTypeClass_forallE_eq (L := [n, m]) (Γ := Γf) henv hΓf haTy hrespectB]
    exact hcRespectB
  let lra : VLevel := .imax (.param 0) (.succ .zero)
  let relB : VExpr := .forallE (.bvar 5) (.forallE (.bvar 6) (.sort .zero))
  have hRVar : env.HasType 2 Γb (.bvar 4) relB := by
    simp only [Γb, relB, fn, β, rel, α]
    exact .bvar (by lookup_tac)
  have hRelBTy : env.HasType 2 Γb relB (.sort lrel) := by
    simp only [relB, lrel]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hcRVar : safeTermClass env Γb [n, m] (.bvar 4) ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓb hRVar hRelBTy
      (by simp [lrel, VLevel.eval, Nat.imax])
  let rAType : VExpr := .forallE (.bvar 5) (.sort .zero)
  have hRA : env.HasType 2 Γb ((VExpr.bvar 4).app (.bvar 1)) rAType := by
    simp only [Γb, rAType, fn, β, rel, α]
    type_tac
  have hRATy : env.HasType 2 Γb rAType (.sort lra) := by
    simp only [rAType, lra]
    apply VEnv.HasType.forallE
    · type_tac
    · exact .sort trivial
  have hcRA : safeTermClass env Γb [n, m]
      ((VExpr.bvar 4).app (.bvar 1)) ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓb hRA hRATy (by simp [lra, VLevel.eval, Nat.imax])
  let lfn : VLevel := .imax (.param 0) (.param 1)
  let fnH : VExpr := fn.lift.lift.lift.lift
  have hFVar : env.HasType 2 Γh (.bvar 3) fnH := by
    simp only [Γh, fnH, rab, fn, β, rel, α]
    exact .bvar (by lookup_tac)
  have hFnHTy : env.HasType 2 Γh fnH (.sort lfn) := by
    simp only [fnH, fn, lfn]
    apply VEnv.HasType.forallE <;> type_tac
  have hcFVar : safeTermClass env Γh [n, m] (.bvar 3) = 0 ↔ m = 0 := by
    rw [safeTermClass_eq_zero_iff_of_hasType (L := [n, m]) henv hΓh hFVar hFnHTy]
    cases m <;> simp [lfn, VLevel.eval, Nat.imax]
  let eqc : VExpr := .const ``Eq [.param 1]
  let lEqTail : VLevel := .imax (.param 1) (.succ .zero)
  let lEqB : VLevel := .imax (.param 1) lEqTail
  let lEqc : VLevel := .imax (.succ (.param 1)) lEqB
  have hEqc : env.HasType 2 Γh eqc (eqConst.type.instL [.param 1]) :=
    VEnv.HasType.const (U := 2) hEqDecl (by decide) (by decide)
  have hEqcTy : env.HasType 2 Γh (eqConst.type.instL [.param 1]) (.sort lEqc) := by
    simpa [eqConst, VExpr.instL, VLevel.inst] using (show env.HasType 2 Γh
      (.forallE (.sort (.param 1))
        (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero))))
      (.sort lEqc) from by
        simp only [lEqc, lEqB, lEqTail]
        apply VEnv.HasType.forallE
        · exact .sort (by decide)
        · apply VEnv.HasType.forallE
          · type_tac
          · apply VEnv.HasType.forallE
            · type_tac
            · exact .sort trivial)
  have hcEqc : safeTermClass env Γh [n, m] eqc ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓh hEqc hEqcTy
      (by simp [lEqc, lEqB, lEqTail, VLevel.eval, Nat.imax])
  let eqB : VExpr := eqc.app (.bvar 4)
  let eqBType : VExpr := .forallE (.bvar 4) (.forallE (.bvar 5) (.sort .zero))
  have hEqB : env.HasType 2 Γh eqB eqBType := by
    simp only [Γh, eqB, eqBType, eqc, rab, fn, β, rel, α]
    type_tac
  have hEqBTy : env.HasType 2 Γh eqBType (.sort lEqB) := by
    simp only [eqBType, lEqB, lEqTail]
    apply VEnv.HasType.forallE
    · type_tac
    · apply VEnv.HasType.forallE
      · type_tac
      · exact .sort trivial
  have hcEqB : safeTermClass env Γh [n, m] eqB ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓh hEqB hEqBTy
      (by simp [lEqB, lEqTail, VLevel.eval, Nat.imax])
  let fa : VExpr := (VExpr.bvar 3).app (.bvar 2)
  let eqBa : VExpr := eqB.app fa
  let eqBaType : VExpr := .forallE (.bvar 4) (.sort .zero)
  have hEqBa : env.HasType 2 Γh eqBa eqBaType := by
    simp only [Γh, eqBa, eqBaType, eqB, fa, eqc, rab, fn, β, rel, α]
    type_tac
  have hEqBaTy : env.HasType 2 Γh eqBaType (.sort lEqTail) := by
    simp only [eqBaType, lEqTail]
    apply VEnv.HasType.forallE
    · type_tac
    · exact .sort trivial
  have hcEqBa : safeTermClass env Γh [n, m] eqBa ≠ 0 :=
    safeTermClass_ne_zero_of_hasType henv hΓh hEqBa hEqBaTy
      (by simp [lEqTail, VLevel.eval, Nat.imax])
  have hrespectInterp (A r B f : ZFSet.{u}) :
      interp κ env assignment [n, m] [fn, β, rel, α] [f, B, r, A] respect =
        quotLiftRespectValue assignment m A r B f := by
    simp only [respect, interp_forallE]
    have hcRespectB' := hcRespectB
    have hcRespectH' := hcRespectH
    have hcEqApp' := hcEqApp
    simp only [Γa, respectB, respectH] at hcRespectB'
    simp only [Γb, respectH] at hcRespectH'
    simp only [Γh] at hcEqApp'
    simp_rw [hcRespectB', hcRespectH', hcEqApp']
    simp only [piValue, if_true]
    simp only [rab, interp_app, interp_bvar]
    have hcRVar' := hcRVar
    have hcRA' := hcRA
    simp only [Γb] at hcRVar' hcRA'
    simp only [hcRVar', hcRA', if_false, appValue, List.getD_cons_zero,
      List.getD_cons_succ]
    simp only [eqApp, interp_app, interp_const, interp_bvar]
    have hcEqc' := hcEqc
    have hcEqB' := hcEqB
    have hcEqBa' := hcEqBa
    have hcFVar' := hcFVar
    simp only [Γh, rab, eqc, eqB, eqBa, fa] at hcEqc' hcEqB' hcEqBa' hcFVar'
    simp only [hcEqc', hcEqB', hcEqBa', if_false, appValue,
      List.map, VLevel.eval, List.getD_cons_zero, List.getD_cons_succ]
    have happF (x : ZFSet.{u}) :
        (if safeTermClass env
            [((VExpr.bvar 4).app (.bvar 1)).app (.bvar 0), .bvar 4, .bvar 3,
              fn, β, rel, α] [n, m] (.bvar 3) = 0 then bullet else depApp f x) =
          appValue m f x := by
      change appValue (safeTermClass env
        [((VExpr.bvar 4).app (.bvar 1)).app (.bvar 0), .bvar 4, .bvar 3,
          fn, β, rel, α] [n, m] (.bvar 3)) f x = appValue m f x
      exact appValue_congr_zero hcFVar' f x
    simp_rw [happF]
    rfl
  change quotLiftConstValue κ n m ∈ interp κ env assignment [n, m] [] []
    (.forallE α bodyR)
  simp only [interp_forallE]
  rw [piValue_congr_zero hcBodyR]
  simp only [α, interp_sort, interpLevel, VLevel.eval, List.getD_cons_zero]
  simp only [bodyR, interp_forallE]
  simp_rw [piValue_congr_zero (by simpa only [Γr, α] using hcBodyB)]
  simp only [bodyB, interp_forallE]
  simp_rw [piValue_congr_zero (by simpa only [Γβ, α] using hcBodyF)]
  simp only [bodyF, interp_forallE]
  simp_rw [piValue_congr_zero (by simpa only [Γf, α] using hcBodyC)]
  simp only [bodyC, interp_forallE]
  simp_rw [piValue_congr_zero (by simpa only [Γc, α] using hcResult)]
  simp only [result, interp_forallE]
  simp_rw [piValue_congr_zero (by simpa only [Γq, α] using hcRes)]
  have hcFnCod' := hcFnCod
  simp only [β, rel, α] at hcFnCod'
  have hrelation' (A : ZFSet.{u}) :
      interp κ env assignment [n, m] [.sort (.param 0)] [A] rel = relationSpace A := by
    simpa only [α] using hrelation A
  simp_rw [hrelation']
  simp only [rel, β, fn, interp_forallE, interp_sort, interp_bvar,
    interpLevel, VLevel.eval, List.getD_cons_zero, List.getD_cons_succ]
  simp_rw [piValue_congr_zero hcFnCod']
  apply quotLiftConstValue_mem_of_domains
  · intro A hA r hr B hB f hf
    have hrespectInterp' := hrespectInterp A r B f
    simp only [fn, β, rel, α] at hrespectInterp'
    rw [hrespectInterp', quotRespectsType_eq hEq hr hB hf]
  · intro A hA r hr B hB f hf c _
    have hquotInterp' := hquotInterp A r B f c hA hr
    simp only [fn, β, rel, α] at hquotInterp'
    exact hquotInterp'

end Lean4LeanModel
