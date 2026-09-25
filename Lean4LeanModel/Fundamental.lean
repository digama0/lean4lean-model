import Lean4LeanModel.ContextConversion
import Lean4Lean.Theory.Typing.Strong

/-! # Fundamental semantic theorem -/

namespace Lean4LeanModel

open Lean4Lean

universe u

/-- Equality and type membership delivered by semantic soundness. -/
structure SemSound (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (L : List Nat) (Γ : List VExpr) (γ : List ZFSet.{u})
    (e₁ e₂ A : VExpr) : Prop where
  eq : interp κ env assignment L Γ γ e₁ = interp κ env assignment L Γ γ e₂
  mem : interp κ env assignment L Γ γ e₁ ∈ interp κ env assignment L Γ γ A

private theorem eval_map_eq_of_forall₂ {L : List Nat} {ls ls' : List VLevel}
    (h : List.Forall₂ (· ≈ ·) ls ls') :
    ls.map (VLevel.eval L) = ls'.map (VLevel.eval L) := by
  induction h with
  | nil => rfl
  | cons hl _ ih =>
    simp only [List.map_cons]
    rw [VLevel.equiv_def.1 hl L, ih]

/-- Semantic soundness for the strengthened typing relation.  The strengthened relation exposes
the well-formedness premises needed by the dependent semantic clauses. -/
theorem fundamentalStrong {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {e₁ e₂ A : VExpr} (M : ModelSetup κ env assignment)
    (H : env.IsDefEqStrong L.length Γ e₁ e₂ A)
    (hΓ : OnCtx Γ (env.IsType L.length)) {γ : List ZFSet.{u}}
    (hγ : ModelsCtx κ env assignment L Γ γ) :
    SemSound κ env assignment L Γ γ e₁ e₂ A := by
  induction H generalizing γ with
  | bvar hlookup _ _ ih =>
    exact ⟨rfl, hγ.lookup M.envWF hΓ hlookup⟩
  | symm _ ih =>
    have s := ih hΓ hγ
    exact ⟨s.eq.symm, s.eq.symm ▸ s.mem⟩
  | trans _ _ ih₁ ih₂ =>
    have s₁ := ih₁ hΓ hγ
    have s₂ := ih₂ hΓ hγ
    exact ⟨s₁.eq.trans s₂.eq, s₁.mem⟩
  | sortDF _ _ heq =>
    exact ⟨interpLevel_equiv heq,
      satisfies_sort M.cardinals_strictMono M.cardinals_inaccessible _ _ _ _⟩
  | @constDF c ci ls ls' u Γ hc hls hls' hlen hlevels _ _ hty _ ihty =>
    have hns := eval_map_eq_of_forall₂ (L := L) hlevels
    have hty₀ : env.HasType L.length Γ (ci.type.instL ls) (.sort u) :=
      hty.defeq.hasType.1
    have hconst : env.IsDefEq L.length Γ (.const c ls) (.const c ls')
        (ci.type.instL ls) := .constDF hc hls hls' hlen hlevels
    have heq : interp κ env assignment L Γ γ (.const c ls) =
        interp κ env assignment L Γ γ (.const c ls') := by
      simp only [interp_const, safeTermClass_eq hΓ]
      rw [termClass_congr M.envWF hΓ hconst hty₀, hns]
    let ns := ls.map (VLevel.eval L)
    have hnslen : ns.length = ci.uvars := by simp [ns, hlen]
    have hval : assignment.constVal c ns ∈
        interp κ env assignment ns [] [] ci.type :=
      M.assignmentWF.const_mem hc hnslen
    obtain ⟨w, hci⟩ := M.envOrdered.constWF hc
    have hciWF : ci.type.WF env ls.length [] := by
      rw [hlen]
      exact ⟨.sort w, hci⟩
    have halign : interp κ env assignment L Γ γ (ci.type.instL ls) =
        interp κ env assignment ns [] [] ci.type := by
      simpa [ns] using interp_closed_instL M.envWF hΓ hγ.length_eq hls hciWF
        (M.envOrdered.closedC hc)
    by_cases hz : safeTermClass env Γ L (.const c ls) = 0
    · have hconstTy : env.HasType L.length Γ (.const c ls) (ci.type.instL ls) :=
        hconst.hasType.1
      have hzero : typeClass env Γ L (ci.type.instL ls) = 0 := by
        rw [← termClass_eq_typeClass_of_hasType M.envWF hΓ hconstTy hty₀]
        simpa [safeTermClass_eq hΓ] using hz
      have hu : u.eval L = 0 :=
        (typeClass_eq_zero_iff_of_hasType M.envWF hΓ hty₀).1 hzero
      have sty := ihty hΓ hγ
      have hp : interp κ env assignment L Γ γ (ci.type.instL ls) ∈ propUniverse := by
        simpa only [interp_sort, interpLevel, hu, ModelUniverse_zero] using sty.mem
      have hbullet : bullet ∈ interp κ env assignment L Γ γ (ci.type.instL ls) := by
        have hv' : assignment.constVal c ns ∈
            interp κ env assignment L Γ γ (ci.type.instL ls) := halign ▸ hval
        exact (eq_bullet_of_mem_prop hp hv') ▸ hv'
      exact ⟨heq, by simpa [interp_const, hz] using hbullet⟩
    · have hv' : assignment.constVal c ns ∈
          interp κ env assignment L Γ γ (ci.type.instL ls) := halign ▸ hval
      exact ⟨heq, by simpa [interp_const, hz, ns] using hv'⟩
  | @appDF Γ A u B v f f' a a' _ _ hA hB hf ha _ ihA ihB ihf iha _ =>
    have hA₀ : env.HasType L.length Γ A (.sort u) := hA.defeq
    have hB₀ : env.HasType L.length (A :: Γ) B (.sort v) := hB.defeq
    have hf₀ : env.IsDefEq L.length Γ f f' (.forallE A B) := hf.defeq
    have ha₀ : env.IsDefEq L.length Γ a a' A := ha.defeq
    have hAB : env.HasType L.length Γ (.forallE A B) (.sort (.imax u v)) :=
      .forallEDF hA₀ hB₀
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA₀⟩
    have sf := ihf hΓ hγ
    have sa := iha hΓ hγ
    have happ : interp κ env assignment L Γ γ (.app f a) ∈
        interp κ env assignment L (A :: Γ)
          (interp κ env assignment L Γ γ a :: γ) B :=
      satisfies_app_fiber M.envWF hΓ hA₀ hB₀ hf₀.hasType.1 sf.mem sa.mem
    have hsubst : interp κ env assignment L Γ γ (B.inst a) =
        interp κ env assignment L (A :: Γ)
          (interp κ env assignment L Γ γ a :: γ) B :=
      interp_inst (κ := κ) (assignment := assignment) M.envWF hΓ
        ha₀.hasType.1 ⟨u, hA₀⟩ ⟨.sort v, hB₀⟩
    have heq : interp κ env assignment L Γ γ (.app f a) =
        interp κ env assignment L Γ γ (.app f' a') := by
      rw [interp_app, interp_app, safeTermClass_eq hΓ, safeTermClass_eq hΓ,
        termClass_congr M.envWF hΓ hf₀ hAB, sf.eq, sa.eq]
    exact ⟨heq, hsubst.symm ▸ happ⟩
  | @lamDF Γ A A' u B v body body' _ _ hA hB hB' hbody hbody'
      ihA ihB ihB' ihbody ihbody' =>
    have hAeq : env.IsDefEq L.length Γ A A' (.sort u) := hA.defeq
    have hA₀ : env.HasType L.length Γ A (.sort u) := hAeq.hasType.1
    have hA'₀ : env.HasType L.length Γ A' (.sort u) := hAeq.hasType.2
    have hB₀ : env.HasType L.length (A :: Γ) B (.sort v) := hB.defeq
    have hb₀ : env.IsDefEq L.length (A :: Γ) body body' B := hbody.defeq
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA₀⟩
    have hctx : VEnv.IsDefEqCtx env L.length Γ (A :: Γ) (A' :: Γ) :=
      .succ .zero hAeq
    have sA := ihA hΓ hγ
    have hbodyMem : ∀ x ∈ interp κ env assignment L Γ γ A,
        interp κ env assignment L (A :: Γ) (x :: γ) body ∈
          interp κ env assignment L (A :: Γ) (x :: γ) B := by
      intro x hx
      exact (ihbody hΓA (hγ.extend hx)).mem
    have hBMem : ∀ x ∈ interp κ env assignment L Γ γ A,
        interp κ env assignment L (A :: Γ) (x :: γ) B ∈ interpLevel κ L v := by
      intro x hx
      exact (ihB hΓA (hγ.extend hx)).mem
    have hmem := satisfies_lam M.envWF hΓ hA₀ hb₀.hasType.1 hB₀ hbodyMem hBMem
    have hclass₁ : safeTermClass env (A :: Γ) L body =
        safeTermClass env (A :: Γ) L body' := by
      rw [safeTermClass_eq hΓA, safeTermClass_eq hΓA]
      exact termClass_congr M.envWF hΓA hb₀ hB₀
    have hclass₂ : safeTermClass env (A :: Γ) L body' =
        safeTermClass env (A' :: Γ) L body' :=
      safeTermClass_defeqCtx M.envOrdered hΓ hctx
    have heq : interp κ env assignment L Γ γ (.lam A body) =
        interp κ env assignment L Γ γ (.lam A' body') := by
      simp only [interp_lam]
      rw [sA.eq, hclass₁, hclass₂]
      apply lamValue_congr
      intro x hx
      calc
        interp κ env assignment L (A :: Γ) (x :: γ) body =
            interp κ env assignment L (A :: Γ) (x :: γ) body' :=
          (ihbody hΓA (hγ.extend (sA.eq ▸ hx))).eq
        _ = interp κ env assignment L (A' :: Γ) (x :: γ) body' :=
          interp_defeqCtx M.envOrdered hΓ hctx _ _
    exact ⟨heq, hmem⟩
  | @forallEDF Γ A A' u body body' v _ _ hA hbody hbody' ihA ihbody ihbody' =>
    have hAeq : env.IsDefEq L.length Γ A A' (.sort u) := hA.defeq
    have hA₀ : env.HasType L.length Γ A (.sort u) := hAeq.hasType.1
    have hA'₀ : env.HasType L.length Γ A' (.sort u) := hAeq.hasType.2
    have hb₀ : env.IsDefEq L.length (A :: Γ) body body' (.sort v) := hbody.defeq
    have hbA₀ : env.HasType L.length (A :: Γ) body (.sort v) := hb₀.hasType.1
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA₀⟩
    have hΓA' : OnCtx (A' :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA'₀⟩
    have hctx : VEnv.IsDefEqCtx env L.length Γ (A :: Γ) (A' :: Γ) :=
      .succ .zero hAeq
    have sA := ihA hΓ hγ
    have hbodyMem : ∀ x ∈ interp κ env assignment L Γ γ A,
        interp κ env assignment L (A :: Γ) (x :: γ) body ∈ interpLevel κ L v := by
      intro x hx
      exact (ihbody hΓA (hγ.extend hx)).mem
    have hmem := satisfies_forallE M.cardinals_strictMono M.cardinals_inaccessible
      M.envWF hΓ hA₀ hbA₀ sA.mem hbodyMem
    have hclass₁ : safeTypeClass env (A :: Γ) L body =
        safeTypeClass env (A :: Γ) L body' := by
      rw [safeTypeClass_eq hΓA, safeTypeClass_eq hΓA]
      exact typeClass_congr M.envWF hΓA hb₀
    have hclass₂ : safeTypeClass env (A :: Γ) L body' =
        safeTypeClass env (A' :: Γ) L body' :=
      safeTypeClass_defeqCtx M.envOrdered hΓ hctx
    have heq : interp κ env assignment L Γ γ (.forallE A body) =
        interp κ env assignment L Γ γ (.forallE A' body') := by
      simp only [interp_forallE]
      rw [sA.eq, hclass₁, hclass₂]
      apply piValue_congr
      intro x hx
      calc
        interp κ env assignment L (A :: Γ) (x :: γ) body =
            interp κ env assignment L (A :: Γ) (x :: γ) body' :=
          (ihbody hΓA (hγ.extend (sA.eq ▸ hx))).eq
        _ = interp κ env assignment L (A' :: Γ) (x :: γ) body' :=
          interp_defeqCtx M.envOrdered hΓ hctx _ _
    exact ⟨heq, hmem⟩
  | defeqDF _ _ _ ihA ihe =>
    have sA := ihA hΓ hγ
    have se := ihe hΓ hγ
    exact ⟨se.eq, sA.eq ▸ se.mem⟩
  | @beta Γ A u B v e a _ _ hA hB he ha _ _ ihA ihB ihe iha _ ihinst =>
    have hA₀ : env.HasType L.length Γ A (.sort u) := hA.defeq
    have hB₀ : env.HasType L.length (A :: Γ) B (.sort v) := hB.defeq
    have he₀ : env.HasType L.length (A :: Γ) e B := he.defeq
    have ha₀ : env.HasType L.length Γ a A := ha.defeq
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA₀⟩
    have sA := ihA hΓ hγ
    have sa := iha hΓ hγ
    have sinst := ihinst hΓ hγ
    have hbody : ∀ x ∈ interp κ env assignment L Γ γ A,
        interp κ env assignment L (A :: Γ) (x :: γ) e ∈
          interp κ env assignment L (A :: Γ) (x :: γ) B := by
      intro x hx
      exact (ihe hΓA (hγ.extend hx)).mem
    have hcod : termClass env (A :: Γ) L e = 0 →
        ∀ x ∈ interp κ env assignment L Γ γ A,
          interp κ env assignment L (A :: Γ) (x :: γ) B ∈ propUniverse := by
      intro hz x hx
      have sB := ihB hΓA (hγ.extend hx)
      have hv : v.eval L = 0 := by
        have hc := termClass_eq_typeClass_of_hasType M.envWF hΓA he₀ hB₀
        exact (typeClass_eq_zero_iff_of_hasType M.envWF hΓA hB₀).1 (hc ▸ hz)
      simpa [interpLevel, hv] using sB.mem
    have hbeta := appValue_lamValue hbody hcod sa.mem
    have hinterp : interp κ env assignment L Γ γ (.app (.lam A e) a) =
        interp κ env assignment L Γ γ (e.inst a) := by
      rw [interp_app, interp_lam, safeTermClass_eq hΓ, safeTermClass_eq hΓA,
        termClass_lam M.envWF hΓ hA₀ he₀ hB₀]
      rw [hbeta]
      exact (interp_inst M.envWF hΓ ha₀ ⟨u, hA₀⟩ ⟨B, he₀⟩).symm
    exact ⟨hinterp, hinterp.symm ▸ sinst.mem⟩
  | @eta Γ A u B v e _ _ hA hB _ he helift _ ihA ihB _ ihe _ _ =>
    have hA₀ : env.HasType L.length Γ A (.sort u) := hA.defeq
    have hB₀ : env.HasType L.length (A :: Γ) B (.sort v) := hB.defeq
    have he₀ : env.HasType L.length Γ e (.forallE A B) := he.defeq
    have helift₀ : env.HasType L.length (A :: Γ) e.lift
        (.forallE A.lift (B.liftN 1 1)) := helift.defeq
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, u, hA₀⟩
    have hbvar : env.HasType L.length (A :: Γ) (.bvar 0) A.lift := .bvar .zero
    have happ : env.HasType L.length (A :: Γ) (.app e.lift (.bvar 0)) B := by
      have happ' := VEnv.IsDefEq.appDF helift₀ hbvar
      rw [VExpr.instN_bvar0] at happ'
      exact happ'
    have hAB : env.HasType L.length Γ (.forallE A B) (.sort (.imax u v)) :=
      .forallEDF hA₀ hB₀
    have se := ihe hΓ hγ
    have hclass : termClass env (A :: Γ) L (.app e.lift (.bvar 0)) =
        typeClass env (A :: Γ) L B :=
      termClass_eq_typeClass_of_hasType M.envWF hΓA happ hB₀
    have hclassLift : termClass env (A :: Γ) L e.lift =
        typeClass env (A :: Γ) L B := by
      calc
        termClass env (A :: Γ) L e.lift = termClass env Γ L e :=
          termClass_weakN M.envWF hΓA Ctx.LiftN.one
        _ = typeClass env Γ L (.forallE A B) :=
          termClass_eq_typeClass_of_hasType M.envWF hΓ he₀ hAB
        _ = typeClass env (A :: Γ) L B :=
          typeClass_forallE M.envWF hΓ hA₀ hB₀
    have hfun : interp κ env assignment L Γ γ e ∈
        piValue (typeClass env (A :: Γ) L B)
          (interp κ env assignment L Γ γ A)
          (fun x => interp κ env assignment L (A :: Γ) (x :: γ) B) := by
      simpa only [interp_forallE, safeTypeClass_eq hΓA] using se.mem
    have heta := lamValue_appValue hfun
    have heq : interp κ env assignment L Γ γ
          (.lam A (.app e.lift (.bvar 0))) = interp κ env assignment L Γ γ e := by
      simp only [interp_lam, interp_app, interp_bvar, List.getD_cons_zero,
        safeTermClass_eq hΓA]
      rw [hclass, hclassLift]
      have hlift : ∀ x, interp κ env assignment L (A :: Γ) (x :: γ) e.lift =
          interp κ env assignment L Γ γ e := fun x => interp_lift M.envWF hΓA x e
      simp_rw [hlift]
      exact heta
    exact ⟨heq, heq.symm ▸ se.mem⟩
  | @proofIrrel Γ p h h' _ _ _ ihp ihh ihh' =>
    have sp := ihp hΓ hγ
    have sh := ihh hΓ hγ
    have sh' := ihh' hΓ hγ
    have hp : interp κ env assignment L Γ γ p ∈ propUniverse := by
      simpa only [interp_sort, interpLevel, VLevel.eval, ModelUniverse_zero] using sp.mem
    exact ⟨(eq_bullet_of_mem_prop hp sh.mem).trans
      (eq_bullet_of_mem_prop hp sh'.mem).symm, sh.mem⟩
  | @extra df ls u Γ hdf hls hlen _ _ _ _ _ _ _ _ _ ihlhs _ =>
    let ns := ls.map (VLevel.eval L)
    have hnslen : ns.length = df.uvars := by simp [ns, hlen]
    obtain ⟨hlty, hrty⟩ := M.envOrdered.defEqWF hdf
    have hlWF : df.lhs.WF env ls.length [] := by
      rw [hlen]
      exact ⟨df.type, hlty⟩
    have hrWF : df.rhs.WF env ls.length [] := by
      rw [hlen]
      exact ⟨df.type, hrty⟩
    have halignL : interp κ env assignment L Γ γ (df.lhs.instL ls) =
        interp κ env assignment ns [] [] df.lhs := by
      simpa [ns] using interp_closed_instL M.envWF hΓ hγ.length_eq hls hlWF
        (hlWF.closedN M.envOrdered trivial)
    have halignR : interp κ env assignment L Γ γ (df.rhs.instL ls) =
        interp κ env assignment ns [] [] df.rhs := by
      simpa [ns] using interp_closed_instL M.envWF hΓ hγ.length_eq hls hrWF
        (hrWF.closedN M.envOrdered trivial)
    have hglobal : interp κ env assignment ns [] [] df.lhs =
        interp κ env assignment ns [] [] df.rhs :=
      M.assignmentWF.defeq hdf hnslen
    exact ⟨halignL.trans (hglobal.trans halignR.symm), (ihlhs hΓ hγ).mem⟩

/-- Fundamental semantic theorem for the public definitional-equality relation. -/
theorem fundamental {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {e₁ e₂ A : VExpr} (M : ModelSetup κ env assignment)
    (H : env.IsDefEq L.length Γ e₁ e₂ A)
    (hΓ : OnCtx Γ (env.IsType L.length)) {γ : List ZFSet.{u}}
    (hγ : ModelsCtx κ env assignment L Γ γ) :
    SemSound κ env assignment L Γ γ e₁ e₂ A :=
  fundamentalStrong M (H.strong M.envOrdered hΓ) hΓ hγ

theorem SemSound.mem₂ {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {γ : List ZFSet.{u}} {e₁ e₂ A : VExpr}
    (h : SemSound κ env assignment L Γ γ e₁ e₂ A) :
    interp κ env assignment L Γ γ e₂ ∈ interp κ env assignment L Γ γ A :=
  h.eq ▸ h.mem

/-- Membership form of the fundamental theorem for a typing judgment. -/
theorem fundamental_hasType {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {L : List Nat} {Γ : List VExpr}
    {e A : VExpr} (M : ModelSetup κ env assignment)
    (H : env.HasType L.length Γ e A)
    (hΓ : OnCtx Γ (env.IsType L.length)) {γ : List ZFSet.{u}}
    (hγ : ModelsCtx κ env assignment L Γ γ) :
    interp κ env assignment L Γ γ e ∈ interp κ env assignment L Γ γ A :=
  (fundamental M H hΓ hγ).mem

end Lean4LeanModel
