module

public import Oberwolfach.MarkedPotentialLoads
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section

/-! The exact equivalence between retaining parent occurrences and taking
canonical marked wheels in the smaller typed host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U E K : Type*} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]
  {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}
  {H₀ Hₖ H₀' Hₖ' : V → U → Prop}

theorem markedCycle_restrict_iff (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) :
    IsMarkedCycleTuple (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b C.val ↔
        ∀ i,Sum.elim PE PK (markedCycleTypedEdge tail head ktail khead m π b C i) := by
  have hinj := markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  constructor
  · intro h i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · obtain ⟨e,he⟩ := h.2.2
      have hh := Classical.choose_spec C.property.2.2
      have heq : Classical.choose C.property.2.2=e.val := hinj.2 (Prod.ext (hh.1.trans he.1.symm) (hh.2.trans he.2.symm))
      simpa only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr,heq] using e.property
    · obtain ⟨e,he⟩ := h.2.1 j
      have hh := Classical.choose_spec (C.property.2.1 j)
      have heq : Classical.choose (C.property.2.1 j)=e.val := hinj.1 (Prod.ext (hh.1.trans he.1.symm) (hh.2.trans he.2.symm))
      simpa only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl,heq] using e.property
  · intro h
    refine ⟨C.property.1,?_,?_⟩
    · intro j
      have hj := h j.castSucc
      simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Sum.elim_inl] at hj
      exact ⟨⟨Classical.choose (C.property.2.1 j),hj⟩,Classical.choose_spec (C.property.2.1 j)⟩
    · have hj := h (Fin.last m)
      simp only [markedCycleTypedEdge,Fin.snoc_last,Sum.elim_inr] at hj
      exact ⟨⟨Classical.choose C.property.2.2,hj⟩,Classical.choose_spec C.property.2.2⟩

theorem markedHub_restrict_iff
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    MarkedHubCompatible H₀' Hₖ' W.1.val W.2.val ↔
      ∀ v∈Set.range W.1.val,H₀' v W.2.val ∨ Hₖ' v W.2.val := by
  constructor
  · intro h v hv
    obtain ⟨i,rfl⟩ := hv
    refine Fin.cases ?_ (fun j=>?_) i
    · exact Or.inr h.1
    · exact Or.inl (h.2 j)
  · intro h
    constructor
    · rcases h (W.1.val 0) ⟨0,rfl⟩ with ho|hk
      · exact False.elim (hdisj _ _ ⟨hH₀ _ _ ho,W.2.property.1⟩)
      · exact hk
    · intro j
      rcases h (W.1.val j.succ) ⟨j.succ,rfl⟩ with ho|hk
      · exact ho
      · exact False.elim (hdisj _ _ ⟨W.2.property.2 j,hHₖ _ _ hk⟩)

theorem markedWheelSurvives_iff_occurrences (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) :
    MarkedWheelSurvives PE PK H₀' Hₖ' W ↔
      ∀ e∈markedOccurrenceResources W,
        Sum.elim (Sum.elim PE PK) (fun vu=>H₀' vu.1 vu.2 ∨ Hₖ' vu.1 vu.2) e := by
  rw [MarkedWheelSurvives,markedCycle_restrict_iff PE PK hp,markedHub_restrict_iff hH₀ hHₖ hdisj]
  constructor
  · rintro ⟨hc,hh⟩ e he
    cases e with
    | inl e =>
      rw [markedOccurrenceResources_rim,markedCycleTypedEdge_mem_iff hp] at he
      obtain ⟨i,rfl⟩ := he
      exact hc i
    | inr vu =>
      rw [markedOccurrenceResources_spoke] at he
      dsimp only [Sum.elim_inr]
      rw [← he.1]
      exact hh vu.1 he.2
  · intro h
    constructor
    · intro i
      apply h (Sum.inl (markedCycleTypedEdge tail head ktail khead m π b W.1 i))
      rw [markedOccurrenceResources_rim,markedCycleTypedEdge_mem_iff hp]
      exact ⟨i,rfl⟩
    · intro v hv
      apply h (Sum.inr (v,W.2.val))
      rw [markedOccurrenceResources_spoke]
      exact ⟨rfl,hv⟩

theorem markedOccurrenceResources_physical
    (W : MarkedWheel tail head ktail khead m π b H₀ Hₖ) (e : (E⊕K)⊕(V×U)) :
    e∈markedOccurrenceResources W ↔
      Sum.map (markedPhysicalEdge tail head ktail khead π) id e∈markedWheelPhysicalResources W := by
  cases e with
  | inl e => simp only [Sum.map_inl,markedOccurrenceResources_rim,markedWheelPhysicalResources_rim]
  | inr vu =>
    rcases vu with ⟨v,u⟩
    simp only [Sum.map_inr,id_eq,markedOccurrenceResources_spoke,markedWheelPhysicalResources_spoke,
      Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range]

theorem markedPotentialLoad_restricted (PE : E → Prop) (PK : K → Prop)
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH₀ : ∀ v u,H₀' v u → H₀ v u) (hHₖ : ∀ v u,Hₖ' v u → Hₖ v u)
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (w : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (e : (E⊕K)⊕(V×U))
    (he : Sum.elim (Sum.elim PE PK) (fun vu=>H₀' vu.1 vu.2 ∨ Hₖ' vu.1 vu.2) e) :
    markedPotentialLoad w (Sum.elim PE PK) (fun v u=>H₀' v u ∨ Hₖ' v u) e =
      ∑ W : MarkedWheel (fun e : {e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e : {e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' Hₖ',
        if Sum.map (markedPhysicalEdge tail head ktail khead π) id e∈markedWheelPhysicalResources W
          then w (markedWheelToLarger PE PK hH₀ hHₖ W) else 0 := by
  rw [markedPotentialLoad,resourceRootOmittedLoad_present _ _ _ e he,
    marked_wheel_restricted_resource_load PE PK hH₀ hHₖ]
  apply Finset.sum_congr rfl
  intro W _
  simp only [← markedWheelSurvives_iff_occurrences PE PK hp hH₀ hHₖ hdisj]
  simp only [markedOccurrenceResources_physical]

end Oberwolfach
