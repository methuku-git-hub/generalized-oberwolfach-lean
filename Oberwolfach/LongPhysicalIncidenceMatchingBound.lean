module

public import Oberwolfach.LongRawPhysicalIncidenceBridge
public import Oberwolfach.LongRawMatchingIncidenceBounds

@[expose] public section
/-! The common raw incidence estimates bound physical rim defects. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_physical_rim_incidence_from_matching_bounds
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀(covered:Finset S) (a γ:ℝ),0≤γ→Fintype.card U≤n→
      (∀i,((longRawIncidenceSet S i\covered).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))→
      ∀x,((rimIncidentResources (f.trans φ) x\covered).card:ℝ)≤2*max a (4*γ)*n:=by
  intro T S f φ covered a γ hγ hu hmatch x
  obtain ⟨haux,_,_⟩:=long_raw_matching_incidence_linear_bounds S covered a γ hγ hu hmatch
  have hsub:rimIncidentResources (f.trans φ) x\covered ⊆
      (longRawIncidenceSet S (.inl x)\covered) ∪ (longRawIncidenceSet S (.inl (π.symm x))\covered):=by
    intro z hz
    have ha: z∈rimIncidentResources (f.trans φ) x:=(Finset.mem_sdiff.mp hz).1
    have hb: z∉covered:=(Finset.mem_sdiff.mp hz).2
    have hh:=long_raw_physical_incidence_subset_two_raw P D π d raw g j x ha
    rcases Finset.mem_union.mp hh with h|h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h,hb⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hb⟩)
  have hcard:((rimIncidentResources (f.trans φ) x\covered).card:ℝ)≤
      ((longRawIncidenceSet S (.inl x)\covered).card:ℝ)+
      ((longRawIncidenceSet S (.inl (π.symm x))\covered).card:ℝ):=by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  linarith [haux x,haux (π.symm x)]
end Oberwolfach
