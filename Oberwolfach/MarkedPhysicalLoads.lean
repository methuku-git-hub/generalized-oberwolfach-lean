module

public import Oberwolfach.MarkedPhysicalCycleProperties
public import Oberwolfach.MarkedSpokeResiduals

@[expose] public section

/-! The typed rim and spoke load equations agree with the actual physical
edge loads. Spoke types are merged only under their disjointness hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 theorem injective_occurrence_sum {I X : Type*} [Fintype I] [DecidableEq X]
    (f : I → X) (hf : Function.Injective f) (x : X) :
    (∑ i,if f i=x then (1:ℝ) else 0)=if x∈Finset.univ.image f then 1 else 0 := by
  classical
  by_cases h : ∃ i,f i=x
  · obtain ⟨i,hi⟩ := h
    have hmem : x∈Finset.univ.image f := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩
    rw [if_pos hmem,Finset.sum_eq_single i]
    · simp only [hi,ite_true]
    · intro j _ hji
      exact if_neg (fun hj=>hji (hf (hj.trans hi.symm)))
    · simp
  · have hmem : x∉Finset.univ.image f := by simpa only [Finset.mem_image,Finset.mem_univ,true_and] using h
    rw [if_neg hmem]
    apply Finset.sum_eq_zero
    intro i _
    exact if_neg (fun hi=>h ⟨i,hi⟩)

variable {V U E K : Type*} [DecidableEq V]
    {tail head : E → V} {ktail khead : K → V} {m : ℕ} {π : Equiv.Perm V} {b : ℕ}

theorem markedCycleIncidence_occurrences
    (hinj : Function.Injective (fun e=>(tail e,head e)))
    (hkinj : Function.Injective (fun e=>(ktail e,khead e)))
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K) :
    markedCycleIncidence tail head ktail khead m C.val e=
      ∑ i,if markedCycleTypedEdge tail head ktail khead m π b C i=e then 1 else 0 := by
  classical
  rw [Fin.sum_univ_castSucc]
  cases e with
  | inl e =>
    simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Fin.snoc_last,Sum.inl.injEq,
      Sum.inr_ne_inl,ite_false,add_zero,markedCycleIncidence,Sum.elim_inl]
    apply Finset.sum_congr rfl
    intro i _
    have hh := Classical.choose_spec (C.property.2.1 i)
    have hs := directedEdgeIndicator_single tail head hinj (Classical.choose (C.property.2.1 i)) e
    simpa only [hh.1,hh.2,eq_comm] using hs
  | inr e =>
    simp only [markedCycleTypedEdge,Fin.snoc_castSucc,Fin.snoc_last,Sum.inr.injEq,
      Sum.inl_ne_inr,ite_false,Finset.sum_const_zero,zero_add,markedCycleIncidence,Sum.elim_inr]
    have hh := Classical.choose_spec C.property.2.2
    have hs := directedEdgeIndicator_single ktail khead hkinj (Classical.choose C.property.2.2) e
    simpa only [hh.1,hh.2,eq_comm] using hs

theorem markedCycleIncidence_physical
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C : MarkedCycleTuple tail head ktail khead m π b) (e : E⊕K) :
    markedCycleIncidence tail head ktail khead m C.val e=
      if markedPhysicalEdge tail head ktail khead π e∈
        markedCyclePhysicalEdges tail head ktail khead m π b C then 1 else 0 := by
  classical
  have hi := markedPhysicalEdge_endpoint_injections tail head ktail khead π hp
  rw [markedCycleIncidence_occurrences hi.1 hi.2]
  have hh := injective_occurrence_sum
    (markedPhysicalEdge tail head ktail khead π ∘ markedCycleTypedEdge tail head ktail khead m π b C)
    (markedCycle_distinct_physical_edges tail head ktail khead m π b hp C)
    (markedPhysicalEdge tail head ktail khead π e)
  simp only [Function.comp_apply,hp.eq_iff] at hh
  change (∑ i,if markedCycleTypedEdge tail head ktail khead m π b C i=e then (1:ℝ) else 0)=_
  convert hh using 1
  simp only [markedCyclePhysicalEdges,Finset.mem_image,Finset.mem_univ,true_and]

theorem markedWheelRimLoad_physical [Fintype V] [Fintype U]
    {H₀ Hₖ : V → U → Prop}
    (hp : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (e : E⊕K) :
    markedWheelRimLoad ψ e=
      ∑ W,if markedPhysicalEdge tail head ktail khead π e∈
        markedCyclePhysicalEdges tail head ktail khead m π b W.1 then ψ W else 0 := by
  unfold markedWheelRimLoad
  apply Finset.sum_congr rfl
  intro W _
  rw [markedCycleIncidence_physical hp]
  split_ifs <;> simp

theorem markedSpokeIndicator_types (C : Fin (m+1) → V) :
    ∀ v,markedSpokeIndicator C false v+markedSpokeIndicator C true v=
      ∑ i : Fin (m+1),if C i=v then (1:ℝ) else 0 := by
  intro v
  rw [Fin.sum_univ_succ]
  simp only [markedSpokeIndicator,Bool.false_eq_true,ite_false,ite_true]
  ring

theorem markedWheelSpokeLoad_physical [Fintype V] [Fintype U] [DecidableEq U]
    {H₀ Hₖ : V → U → Prop}
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ) (v : V) (u : U) :
    markedWheelSpokeLoad ψ false v u+markedWheelSpokeLoad ψ true v u=
      ∑ W,if W.2.val=u ∧ v∈Finset.univ.image W.1.val then ψ W else 0 := by
  unfold markedWheelSpokeLoad
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro W _
  by_cases hu : W.2.val=u
  · simp only [hu,ite_true,true_and]
    rw [← mul_add,markedSpokeIndicator_types,
      injective_occurrence_sum W.1.val (permutationSeparated_injective π b W.1.val W.1.property.1)]
    split_ifs <;> simp
  · simp only [hu,ite_false,false_and,mul_zero,add_zero]

theorem markedWheelSpokeLoad_physical_exact [Fintype V] [Fintype U] [DecidableEq U]
    {H₀ Hₖ : V → U → Prop}
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (hψ : ∀ j v u,markedWheelSpokeLoad ψ j v u=if j then (if Hₖ v u then 1 else 0) else (if H₀ v u then 1 else 0))
    (v : V) (u : U) (he : H₀ v u ∨ Hₖ v u) :
    (∑ W,if W.2.val=u ∧ v∈Finset.univ.image W.1.val then ψ W else 0)=1 := by
  rw [← markedWheelSpokeLoad_physical,hψ false,hψ true]
  have hd := hdisj v u
  simp only [Bool.false_eq_true,ite_false,ite_true]
  rcases he with he|he
  · have hk : ¬Hₖ v u := fun hk=>hd ⟨he,hk⟩
    simp [he,hk]
  · have h0 : ¬H₀ v u := fun h0=>hd ⟨h0,he⟩
    simp [he,h0]

theorem markedSpokeResidual_of_physical_error [Fintype V] [Fintype U] [DecidableEq U]
    {H₀ Hₖ : V → U → Prop}
    (hdisj : ∀ v u,¬(H₀ v u ∧ Hₖ v u))
    (ψ : MarkedWheel tail head ktail khead m π b H₀ Hₖ → ℝ)
    (η : ℝ) (hη : 0≤η)
    (herr : ∀ v u,H₀ v u ∨ Hₖ v u →
      |(∑ W,if W.2.val=u ∧ v∈Finset.univ.image W.1.val then ψ W else 0)-1|≤η) :
    ∀ j v u,|markedSpokeResidual ψ j v u|≤η := by
  intro j v u
  have he := herr v u
  rw [← markedWheelSpokeLoad_physical] at he
  have hd := hdisj v u
  cases j
  · by_cases h0 : H₀ v u
    · have hk : ¬Hₖ v u := fun hk=>hd ⟨h0,hk⟩
      have hz := markedWheelSpokeLoad_outside ψ true v u hk
      have hh := he (Or.inl h0)
      rw [hz,add_zero,abs_sub_comm] at hh
      simpa only [markedSpokeResidual,Bool.false_eq_true,ite_false,if_pos h0] using hh
    · have hz := markedWheelSpokeLoad_outside ψ false v u h0
      simpa only [markedSpokeResidual,Bool.false_eq_true,ite_false,if_neg h0,hz,sub_self,abs_zero] using hη
  · by_cases hk : Hₖ v u
    · have h0 : ¬H₀ v u := fun h0=>hd ⟨h0,hk⟩
      have hz := markedWheelSpokeLoad_outside ψ false v u h0
      have hh := he (Or.inr hk)
      rw [hz,zero_add,abs_sub_comm] at hh
      simpa only [markedSpokeResidual,ite_true,if_pos hk] using hh
    · have hz := markedWheelSpokeLoad_outside ψ true v u hk
      simpa only [markedSpokeResidual,ite_true,if_neg hk,hz,sub_self,abs_zero] using hη

end Oberwolfach
