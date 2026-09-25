import Lean4LeanModel.ModelConstructionDebt
import Lean4LeanModel.StandardAxioms

/-! # Construction of semantic assignments -/

namespace Lean4LeanModel

open Lean4Lean

universe u

namespace Assignment

/-- `assignment'` preserves the meanings of every constant already present in `env`. -/
def Extends (env : VEnv) (assignment assignment' : Assignment.{u}) : Prop :=
  ∀ {c ci}, env.constants c = some ci → ∀ ns,
    assignment'.constVal c ns = assignment.constVal c ns

theorem Extends.rfl (env : VEnv) (assignment : Assignment.{u}) :
    Extends env assignment assignment := by
  intro c ci hc ns
  rfl

/-- Replace the semantic value of one constant name. -/
noncomputable def set (assignment : Assignment.{u}) (name : Name)
    (value : List Nat → ZFSet.{u}) : Assignment.{u} where
  constVal c ns := if c = name then value ns else assignment.constVal c ns

@[simp] theorem set_self (assignment : Assignment.{u}) (name : Name)
    (value : List Nat → ZFSet.{u}) (ns : List Nat) :
    (assignment.set name value).constVal name ns = value ns := by
  simp [set]

theorem set_other (assignment : Assignment.{u}) {name c : Name}
    (value : List Nat → ZFSet.{u}) (h : c ≠ name) (ns : List Nat) :
    (assignment.set name value).constVal c ns = assignment.constVal c ns := by
  simp [set, h]

end Assignment

private theorem safeTermClass_mono {env env' : VEnv} {L : List Nat}
    {Γ : List VExpr} {e : VExpr} (hle : env ≤ env')
    (henv : env.WF) (henv' : env'.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (he : e.WF env L.length Γ) :
    safeTermClass env' Γ L e = safeTermClass env Γ L e := by
  have hΓ' : OnCtx Γ (env'.IsType L.length) := hΓ.mono fun h => h.mono hle
  obtain ⟨A, heA⟩ := he
  obtain ⟨lvl, hA⟩ := heA.isType henv hΓ
  rw [safeTermClass_eq hΓ', safeTermClass_eq hΓ]
  unfold termClass
  exact congrArg classLevel (propext
    (isProofTerm_mono_iff hle henv hΓ henv' hΓ' heA hA))

private theorem safeTypeClass_mono {env env' : VEnv} {L : List Nat}
    {Γ : List VExpr} {A : VExpr} (hle : env ≤ env')
    (henv : env.WF) (henv' : env'.WF) (hΓ : OnCtx Γ (env.IsType L.length))
    (hA : env.IsType L.length Γ A) :
    safeTypeClass env' Γ L A = safeTypeClass env Γ L A := by
  have hΓ' : OnCtx Γ (env'.IsType L.length) := hΓ.mono fun h => h.mono hle
  obtain ⟨lvl, hA⟩ := hA
  rw [safeTypeClass_eq hΓ', safeTypeClass_eq hΓ]
  unfold typeClass
  exact congrArg classLevel (propext
    (isPropType_mono_iff hle henv hΓ henv' hΓ' hA))

/-- Interpretation of an old well-formed expression is unchanged by an environment extension
whose assignment preserves all old constants. -/
theorem interp_extension {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment assignment' : Assignment.{u}} {L : List Nat}
    {Γ : List VExpr} {γ : List ZFSet.{u}} (hle : env ≤ env')
    (henv : env.WF) (henv' : env'.WF)
    (hassign : Assignment.Extends env assignment assignment')
    (hΓ : OnCtx Γ (env.IsType L.length)) (e : VExpr)
    (he : e.WF env L.length Γ) :
    interp κ env' assignment' L Γ γ e = interp κ env assignment L Γ γ e := by
  induction e generalizing Γ γ with
  | bvar => rfl
  | sort => rfl
  | const c ls =>
    obtain ⟨ci, hc, _, _⟩ := he.const_inv henv.ordered hΓ
    simp only [interp_const]
    rw [safeTermClass_mono hle henv henv' hΓ he, hassign hc]
  | app f a ihf iha =>
    obtain ⟨A, B, hf, ha⟩ := he.app_inv henv.ordered hΓ
    simp only [interp_app]
    rw [safeTermClass_mono hle henv henv' hΓ ⟨_, hf⟩,
      ihf hΓ ⟨_, hf⟩, iha hΓ ⟨_, ha⟩]
  | lam A body ihA ihbody =>
    obtain ⟨hA, hbody⟩ := he.lam_inv henv.ordered hΓ
    have hAwf : A.WF env L.length Γ := by
      obtain ⟨lvl, hA⟩ := hA
      exact ⟨.sort lvl, hA⟩
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, hA⟩
    simp only [interp_lam]
    rw [safeTermClass_mono hle henv henv' hΓA hbody, ihA hΓ hAwf]
    apply lamValue_congr
    intro x _
    exact ihbody hΓA hbody
  | forallE A body ihA ihbody =>
    obtain ⟨V, hfor⟩ := he
    obtain ⟨hA, hbody⟩ := VEnv.HasType.forallE_inv henv hfor
    have hAwf : A.WF env L.length Γ := by
      obtain ⟨lvl, hA⟩ := hA
      exact ⟨.sort lvl, hA⟩
    have hbodywf : body.WF env L.length (A :: Γ) := by
      obtain ⟨lvl, hbody⟩ := hbody
      exact ⟨.sort lvl, hbody⟩
    have hΓA : OnCtx (A :: Γ) (env.IsType L.length) := ⟨hΓ, hA⟩
    simp only [interp_forallE]
    rw [safeTypeClass_mono hle henv henv' hΓA hbody, ihA hΓ hAwf]
    apply piValue_congr
    intro x _
    exact ihbody hΓA hbodywf

/-- A successful constant insertion starts from a fresh name. -/
theorem addConst_fresh {env env' : VEnv} {name : Name} {ci : VConstant}
    (hadd : env.addConst name ci = some env') : env.constants name = none := by
  unfold VEnv.addConst at hadd
  split at hadd <;> simp_all

/-- Every constant after an insertion is either the new constant or an old one. -/
theorem addConst_lookup_cases {env env' : VEnv} {name c : Name}
    {ci cj : VConstant} (hadd : env.addConst name ci = some env')
    (hc : env'.constants c = some cj) :
    (c = name ∧ cj = ci) ∨ env.constants c = some cj := by
  unfold VEnv.addConst at hadd
  split at hadd <;> try contradiction
  next hnone =>
    cases hadd
    simp only at hc
    split at hc
    · left
      simp_all
    · right
      exact hc

/-- Inserting a constant does not introduce definitional equations. -/
theorem addConst_defeq_old {env env' : VEnv} {name : Name} {ci : VConstant}
    {df : VDefEq} (hadd : env.addConst name ci = some env')
    (hdf : env'.defeqs df) : env.defeqs df := by
  unfold VEnv.addConst at hadd
  split at hadd <;> try contradiction
  cases hadd
  exact hdf

theorem Assignment.Extends.set_of_addConst {env env' : VEnv} {assignment : Assignment.{u}}
    {name : Name} {ci : VConstant} (value : List Nat → ZFSet.{u})
    (hadd : env.addConst name ci = some env') :
    Assignment.Extends env assignment (assignment.set name value) := by
  intro c cj hc ns
  apply Assignment.set_other
  intro h
  subst c
  rw [addConst_fresh hadd] at hc
  contradiction

/-- Add a constant whose semantic value has already been shown to inhabit its declared type. -/
theorem assignmentWF_addConst_sem {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {name : Name} {ci : VConstant}
    (meaning : List Nat → ZFSet.{u}) (M : ModelSetup κ env assignment)
    (hadd : env.addConst name ci = some env') (henv' : env'.WF)
    (hmeaning : ∀ ns, ns.length = ci.uvars →
      meaning ns ∈ interp κ env' (assignment.set name meaning) ns [] [] ci.type) :
    (assignment.set name meaning).WF κ env' := by
  let assignment' := assignment.set name meaning
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  constructor
  · intro c cj ns hc hns
    rcases addConst_lookup_cases hadd hc with hnew | hcOld
    · obtain ⟨hcname, hcj⟩ := hnew
      subst c
      subst cj
      simpa [assignment'] using hmeaning ns hns
    · have hOld := M.assignmentWF.const_mem hcOld hns
      obtain ⟨lvl, hciOld⟩ := M.envOrdered.constWF hcOld
      have hciOldWF : cj.type.WF env cj.uvars [] := ⟨.sort lvl, hciOld⟩
      have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial cj.type (by simpa [hns] using hciOldWF)
      have hvalEq := hext hcOld ns
      exact hvalEq.symm ▸ htypeExt.symm ▸ hOld
  · intro df ns hdf hns
    have hdfOld := addConst_defeq_old hadd hdf
    have hOld := M.assignmentWF.defeq hdfOld hns
    obtain ⟨hl, hr⟩ := M.envOrdered.defEqWF hdfOld
    have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
      (L := ns) (Γ := []) (γ := []) trivial df.lhs (by
        simpa [hns] using show df.lhs.WF env df.uvars [] from ⟨df.type, hl⟩)
    have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
      (L := ns) (Γ := []) (γ := []) trivial df.rhs (by
        simpa [hns] using show df.rhs.WF env df.uvars [] from ⟨df.type, hr⟩)
    exact hlExt.trans (hOld.trans hrExt.symm)

/-! ## Semantic axiom interface -/

/-- A semantic value for an axiom declaration, stated in the environment before the declaration is
added. `model_addAxiom` transports the type interpretation to the extended environment. -/
structure AxiomMeaning (κ : ℕ → Cardinal.{u}) (env : VEnv) (assignment : Assignment.{u})
    (ci : VConstVal) where
  value : List Nat → ZFSet.{u}
  valid : ∀ ns, ns.length = ci.uvars →
    value ns ∈ interp κ env assignment ns [] [] ci.type

/-- A handler is the only interface the declaration-history induction needs for axioms. The
predicate `P` is completely abstract, so an upstream allowed-axiom condition only needs to provide
an adapter to a suitable handler. -/
def AxiomHandler (κ : ℕ → Cardinal.{u}) (P : VConstVal → Prop) : Prop :=
  ∀ {env env' : VEnv} {assignment : Assignment.{u}} {ci : VConstVal},
    ModelSetup κ env assignment →
    ci.toVConstant.WF env →
    env.addConst ci.name ci.toVConstant = some env' →
    env'.WF → P ci →
    ∃ assignment', ModelSetup κ env' assignment'

/-- Add an axiom for which a semantic meaning has been supplied. -/
theorem model_addAxiom {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {ci : VConstVal}
    (M : ModelSetup κ env assignment) (hci : ci.toVConstant.WF env)
    (hadd : env.addConst ci.name ci.toVConstant = some env') (henv' : env'.WF)
    (meaning : AxiomMeaning κ env assignment ci) :
    ∃ assignment', ModelSetup κ env' assignment' := by
  let assignment' := assignment.set ci.name meaning.value
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  obtain ⟨lvl, htype⟩ := hci
  have htypeWF : ci.type.WF env ci.uvars [] := ⟨.sort lvl, htype⟩
  refine ⟨assignment', M.cardinals_strictMono, M.cardinals_inaccessible, henv', ?_⟩
  apply assignmentWF_addConst_sem meaning.value M hadd henv'
  intro ns hns
  have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
    (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using htypeWF)
  simpa [assignment'] using htypeExt.symm ▸ meaning.valid ns hns

namespace AxiomMeaning

/-- A provider constructs semantic meanings for every axiom satisfying `P`. -/
def Provider (κ : ℕ → Cardinal.{u}) (P : VConstVal → Prop) :=
  ∀ {env : VEnv} {assignment : Assignment.{u}} {ci : VConstVal},
    P ci → ModelSetup κ env assignment → ci.toVConstant.WF env →
    AxiomMeaning κ env assignment ci

/-- Restrict a provider along an implication between axiom predicates. -/
def Provider.map {κ : ℕ → Cardinal.{u}} {P Q : VConstVal → Prop}
    (provider : Provider κ Q) (hpq : ∀ ci, P ci → Q ci) : Provider κ P := by
  intro env assignment ci hP M hci
  exact provider (hpq ci hP) M hci

/-- Every provider induces the handler consumed by declaration-history construction. -/
def Provider.toHandler {κ : ℕ → Cardinal.{u}} {P : VConstVal → Prop}
    (provider : Provider κ P) : AxiomHandler κ P := by
  intro env env' assignment ci M hci hadd henv' hP
  exact model_addAxiom M hci hadd henv' (provider hP M hci)

end AxiomMeaning

namespace StandardAxiom

/-- The construction hook required for histories containing only the standard three axioms.

This is intentionally a handler, rather than three meanings quantified over arbitrary
`ModelSetup`s. The latter would be unprovable until the model records canonical interpretations of
`Eq`, `Iff`, `Nonempty`, and quotients. The future inductive/quotient construction can establish
that stronger invariant and implement this hook without changing the policy-facing API. -/
abbrev Handler (κ : ℕ → Cardinal.{u}) := AxiomHandler κ IsStandardAxiom

end StandardAxiom

/-- A stored, well-typed declaration value supplies the meaning of a newly added constant. -/
theorem assignmentWF_addConst {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {name : Name} {ci : VConstant} {value : VExpr}
    (M : ModelSetup κ env assignment)
    (hvalue : env.HasType ci.uvars [] value ci.type)
    (hadd : env.addConst name ci = some env') (henv' : env'.WF) :
    let assignment' := assignment.set name fun ns =>
      interp κ env assignment ns [] [] value
    assignment'.WF κ env' := by
  let assignment' := assignment.set name fun ns => interp κ env assignment ns [] [] value
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  have htype : env.IsType ci.uvars [] ci.type := hvalue.isType M.envWF trivial
  have htypeWF : ci.type.WF env ci.uvars [] := by
    obtain ⟨lvl, htype⟩ := htype
    exact ⟨.sort lvl, htype⟩
  apply assignmentWF_addConst_sem
    (fun ns => interp κ env assignment ns [] [] value) M hadd henv'
  intro ns hns
  have hvalueNs : env.HasType ns.length [] value ci.type := by simpa [hns] using hvalue
  have hmem := fundamental_hasType M hvalueNs trivial ModelsCtx.nil
  have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
    (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using htypeWF)
  simpa [assignment'] using htypeExt.symm ▸ hmem

/-- The meaning assigned to a newly added constant agrees with its stored declaration value. -/
theorem interp_addedConst_eq {κ : ℕ → Cardinal.{u}} {env env' : VEnv}
    {assignment : Assignment.{u}} {name : Name} {ci : VConstant} {value : VExpr}
    (M : ModelSetup κ env assignment)
    (hvalue : env.HasType ci.uvars [] value ci.type)
    (hadd : env.addConst name ci = some env') (henv' : env'.WF)
    (ns : List Nat) (hns : ns.length = ci.uvars) :
    let assignment' := assignment.set name fun ns =>
      interp κ env assignment ns [] [] value
    interp κ env' assignment' ns [] [] (.const name (VLevel.params ci.uvars)) =
      interp κ env' assignment' ns [] [] value := by
  let assignment' := assignment.set name fun ns => interp κ env assignment ns [] [] value
  have hle := VEnv.addConst_le hadd
  have hext : Assignment.Extends env assignment assignment' :=
    Assignment.Extends.set_of_addConst _ hadd
  have hvalueNs : env.HasType ns.length [] value ci.type := by simpa [hns] using hvalue
  have hvalueNs' := hvalueNs.mono hle
  obtain ⟨lvl, htypeNs⟩ := VEnv.IsDefEq.isType M.envOrdered
    (Γ := []) (U := ns.length) trivial hvalueNs
  have htypeNs' := htypeNs.mono hle
  have hconst : env'.HasType ns.length [] (.const name (VLevel.params ci.uvars)) ci.type :=
    by
      rw [← (hvalue.levelWF trivial).2.2.instL_id]
      simpa [hns] using VEnv.HasType.const (Γ := []) (VEnv.addConst_self hadd)
        (VLevel.params_wf (n := ci.uvars)) VLevel.params_length
  have hclass : termClass env' [] ns (.const name (VLevel.params ci.uvars)) =
      termClass env' [] ns value := by
    calc
      _ = typeClass env' [] ns ci.type :=
        termClass_eq_typeClass_of_hasType (L := ns) (Γ := []) henv' trivial hconst htypeNs'
      _ = termClass env' [] ns value :=
        (termClass_eq_typeClass_of_hasType (L := ns) (Γ := []) henv'
          trivial hvalueNs' htypeNs').symm
  have hvalueExt : interp κ env' assignment' ns [] [] value =
      interp κ env assignment ns [] [] value :=
    interp_extension (κ := κ) (L := ns) (Γ := []) (γ := [])
      hle M.envWF henv' hext trivial value ⟨ci.type, hvalueNs⟩
  by_cases hz : safeTermClass env' [] ns (.const name (VLevel.params ci.uvars)) = 0
  · have hzero : typeClass env [] ns ci.type = 0 := by
      have hΓ' : OnCtx [] (env'.IsType ns.length) := trivial
      have hmono := safeTypeClass_mono (L := ns) (Γ := [])
        hle M.envWF henv' trivial ⟨lvl, htypeNs⟩
      rw [safeTypeClass_eq hΓ', safeTypeClass_eq (show OnCtx [] (env.IsType ns.length) from trivial)] at hmono
      rw [← hmono]
      rw [← termClass_eq_typeClass_of_hasType (L := ns) (Γ := [])
        henv' trivial hconst htypeNs']
      simpa [safeTermClass_eq (show OnCtx [] (env'.IsType ns.length) from trivial)] using hz
    have hlvl : lvl.eval ns = 0 :=
      (typeClass_eq_zero_iff_of_hasType (L := ns) (Γ := [])
        M.envWF trivial htypeNs).1 hzero
    have htypeMem := fundamental_hasType M htypeNs trivial ModelsCtx.nil
    have hprop : interp κ env assignment ns [] [] ci.type ∈ propUniverse := by
      simpa only [interp_sort, interpLevel, hlvl, ModelUniverse_zero] using htypeMem
    have hvalueMem := fundamental_hasType M hvalueNs trivial ModelsCtx.nil
    have hbullet : interp κ env assignment ns [] [] value = bullet :=
      eq_bullet_of_mem_prop hprop hvalueMem
    simp only [interp_const, hz, if_pos]
    exact (hvalueExt.trans hbullet).symm
  · simp only [interp_const, hz]
    rw [Assignment.set_self]
    have hparams : (VLevel.params ci.uvars).map (VLevel.eval ns) = ns := by
      apply List.ext_get (by simp [hns, VLevel.params])
      intro i hi hj
      simp [VLevel.params, VLevel.eval, List.getD_eq_getElem?_getD, hj]
    rw [hparams]
    exact hvalueExt.symm

/-- Add one already validated primitive equation without changing the assignment. -/
theorem assignmentWF_addDefEq {κ : ℕ → Cardinal.{u}} {env : VEnv}
    {assignment : Assignment.{u}} {df : VDefEq}
    (M : ModelSetup κ env assignment)
    (hdfWF : df.WF env)
    (hsem : ∀ ns, ns.length = df.uvars →
      interp κ env assignment ns [] [] df.lhs =
        interp κ env assignment ns [] [] df.rhs)
    (henv' : (env.addDefEq df).WF) :
    assignment.WF κ (env.addDefEq df) := by
  have hle : env ≤ env.addDefEq df := VEnv.addDefEq_le
  have hext : Assignment.Extends env assignment assignment := Assignment.Extends.rfl _ _
  constructor
  · intro c ci ns hc hns
    have hOld := M.assignmentWF.const_mem hc hns
    obtain ⟨lvl, hci⟩ := M.envOrdered.constWF hc
    have hciWF : ci.type.WF env ci.uvars [] := ⟨.sort lvl, hci⟩
    have htypeExt := interp_extension (κ := κ) hle M.envWF henv' hext
      (L := ns) (Γ := []) (γ := []) trivial ci.type (by simpa [hns] using hciWF)
    exact htypeExt.symm ▸ hOld
  · intro df' ns hdf' hns
    rcases hdf' with hnew | hdfOld
    · subst df'
      have hOld := hsem ns hns
      obtain ⟨hl, hr⟩ := hdfWF
      have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df.lhs (by
          simpa [hns] using show df.lhs.WF env df.uvars [] from ⟨df.type, hl⟩)
      have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df.rhs (by
          simpa [hns] using show df.rhs.WF env df.uvars [] from ⟨df.type, hr⟩)
      exact hlExt.trans (hOld.trans hrExt.symm)
    · have hOld := M.assignmentWF.defeq hdfOld hns
      obtain ⟨hl, hr⟩ := M.envOrdered.defEqWF hdfOld
      have hlExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df'.lhs (by
          simpa [hns] using show df'.lhs.WF env df'.uvars [] from ⟨df'.type, hl⟩)
      have hrExt := interp_extension (κ := κ) hle M.envWF henv' hext
        (L := ns) (Γ := []) (γ := []) trivial df'.rhs (by
          simpa [hns] using show df'.rhs.WF env df'.uvars [] from ⟨df'.type, hr⟩)
      exact hlExt.trans (hOld.trans hrExt.symm)

/-! ## Declaration-history construction -/

/-- Build a semantic assignment along a well-formed declaration history using an abstract axiom
predicate and handler. Definitions and opaque constants use their stored values; examples do not
alter the environment. -/
theorem model_of_wfHistory_withAxioms {κ : ℕ → Cardinal.{u}} {P : VConstVal → Prop}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : AxiomHandler κ P) {ds : List VDecl} {env : VEnv}
    (H : VEnv.WF' ds env) (haxioms : AxiomsSatisfy P ds) :
    ∃ assignment, ModelSetup κ env assignment := by
  induction H with
  | empty =>
    refine ⟨Assignment.empty, hκ, hi, ⟨[], .empty⟩, ?_⟩
    constructor
    · intro c ci ns hc
      simp [VEnv.empty] at hc
    · intro df ns hdf
      exact False.elim hdf
  | @decl d env' ds env hd hds ih =>
    obtain ⟨assignment, M⟩ := ih haxioms.tail
    have henv' : env'.WF := ⟨d :: ds, .decl hd hds⟩
    cases hd with
    | «axiom» hci hadd =>
      exact handler M hci hadd henv' haxioms.head
    | @«def» env₁ env ci hci hadd =>
      let assignment₁ := assignment.set ci.name fun ns =>
        interp κ env assignment ns [] [] ci.value
      have henv₁ : env₁.WF :=
        ⟨.opaque ci :: ds, .decl (.opaque hci hadd) hds⟩
      have hassignment₁ : assignment₁.WF κ env₁ := by
        simpa [assignment₁] using
          assignmentWF_addConst M hci hadd henv₁
      have M₁ : ModelSetup κ env₁ assignment₁ :=
        ⟨hκ, hi, henv₁, hassignment₁⟩
      have hdfWF : ci.toDefEq.WF env₁ := by
        constructor
        · simp only [VDefVal.toDefEq]
          rw [← (hci.levelWF trivial).2.2.instL_id]
          exact VEnv.HasType.const (VEnv.addConst_self hadd) VLevel.params_wf
            VLevel.params_length
        · simpa [VDefVal.toDefEq] using hci.mono (VEnv.addConst_le hadd)
      have hsem : ∀ ns, ns.length = ci.toDefEq.uvars →
          interp κ env₁ assignment₁ ns [] [] ci.toDefEq.lhs =
            interp κ env₁ assignment₁ ns [] [] ci.toDefEq.rhs := by
        intro ns hns
        simpa [VDefVal.toDefEq, assignment₁] using
          interp_addedConst_eq M hci hadd henv₁ ns hns
      refine ⟨assignment₁, hκ, hi, henv', ?_⟩
      exact assignmentWF_addDefEq M₁ hdfWF hsem henv'
    | @«opaque» _ env ci hci hadd =>
      let assignment' := assignment.set ci.name fun ns =>
        interp κ env assignment ns [] [] ci.value
      refine ⟨assignment', hκ, hi, henv', ?_⟩
      simpa [assignment'] using assignmentWF_addConst M hci hadd henv'
    | «example» hci =>
      exact ⟨assignment, hκ, hi, henv', M.assignmentWF⟩
    | quot hready hadd =>
      exact model_quotient_boundary M hready hadd henv'
    | induct hdecl hadd =>
      exact model_inductive_boundary M hdecl hadd henv'

/-- Build a model when every axiom in the history is one of the standard three and semantic
meanings for those declarations are available. -/
theorem model_of_wfHistory_standard {κ : ℕ → Cardinal.{u}}
    (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ) {ds : List VDecl} {env : VEnv}
    (H : VEnv.WF' ds env) (haxioms : AxiomsSatisfy IsStandardAxiom ds) :
    ∃ assignment, ModelSetup κ env assignment :=
  model_of_wfHistory_withAxioms hκ hi handler H haxioms

/-- Adapter form for any proposed upstream predicate `P`: it is enough to show that `P` permits
only the canonical standard declarations. -/
theorem model_of_wfHistory_of_axiomPredicate {κ : ℕ → Cardinal.{u}}
    {P : VConstVal → Prop} (hκ : StrictMono κ) (hi : ∀ n, (κ n).IsInaccessible)
    (handler : StandardAxiom.Handler κ)
    (toStandard : ∀ ci, P ci → IsStandardAxiom ci)
    {ds : List VDecl} {env : VEnv} (H : VEnv.WF' ds env)
    (haxioms : AxiomsSatisfy P ds) :
    ∃ assignment, ModelSetup κ env assignment :=
  model_of_wfHistory_standard hκ hi handler H (haxioms.mono toStandard)

/-- Build a semantic assignment along an unrestricted well-formed declaration history. The false
arbitrary-axiom case remains isolated in `ModelConstructionDebt`; callers with an allowed-axiom
condition should use `model_of_wfHistory_withAxioms` instead. -/
theorem model_of_wfHistory {κ : ℕ → Cardinal.{u}} (hκ : StrictMono κ)
    (hi : ∀ n, (κ n).IsInaccessible) {ds : List VDecl} {env : VEnv}
    (H : VEnv.WF' ds env) : ∃ assignment, ModelSetup κ env assignment := by
  refine model_of_wfHistory_withAxioms hκ hi (P := fun _ => True) ?_ H ?_
  · intro env env' assignment ci M hci hadd henv' _
    exact model_axiom_boundary M hci hadd henv'
  · exact fun _ _ => trivial

/-- Every well-formed environment has a semantic assignment, modulo the explicitly isolated
axiom, quotient, and upstream-inductive boundaries above. -/
theorem model_of_wf {κ : ℕ → Cardinal.{u}} (hκ : StrictMono κ)
    (hi : ∀ n, (κ n).IsInaccessible) {env : VEnv} (H : env.WF) :
    ∃ assignment, ModelSetup κ env assignment := by
  obtain ⟨ds, hds⟩ := H
  exact model_of_wfHistory hκ hi hds

end Lean4LeanModel
