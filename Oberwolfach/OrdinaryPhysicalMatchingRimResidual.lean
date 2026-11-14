module

public import Oberwolfach.OrdinaryPhysicalMatchingRows
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! The physical rim rows tested by the same matching bound the actual
unmatched physical rim graph, even when typed arcs share a physical edge. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_physical_matching_rim_residual_degree
    {V U A C:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype C]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq C]
    (φ:A→Sym2 V⊕(V×U)) (R:C→Finset A) (σ:A→Bool)
    (L:Finset (PhysicalSampledCandidate R σ)) (κ:ℝ)
    (hrow:∀v,(((physicalSampledRow φ σ (ordinaryPhysicalRow (.inl v)))\
      L.biUnion (physicalSampledCandidateSet φ R σ)).card:ℝ)≤κ):
    let ι:PhysicalSampledActive φ σ↪Sym2 V⊕(V×U):=Function.Embedding.subtype _
    ∀v,((physicalRimResidualGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))).degree v:ℝ)≤κ:=by
  intro ι v
  have hsub:rimIncidentResources ι v\L.biUnion (physicalSampledCandidateSet φ R σ)⊆
      physicalSampledRow φ σ (ordinaryPhysicalRow (.inl v))\L.biUnion (physicalSampledCandidateSet φ R σ):=by
    intro z hz
    obtain ⟨hz,hnot⟩:=Finset.mem_sdiff.mp hz
    obtain ⟨w,hw,he⟩:=(Finset.mem_filter.mp hz).2
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hnot⟩
    change z.val∈Finset.univ.image (fun x:V=>Sum.inl s(v,x))
    exact Finset.mem_image.mpr ⟨w,Finset.mem_univ _,he.symm⟩
  have hcount:((rimIncidentResources ι v\L.biUnion (physicalSampledCandidateSet φ R σ)).card:ℝ)≤
      ((physicalSampledRow φ σ (ordinaryPhysicalRow (.inl v))\L.biUnion (physicalSampledCandidateSet φ R σ)).card:ℝ):=by
    exact_mod_cast Finset.card_le_card hsub
  have hdegree:((physicalRimResidualGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))).degree v:ℝ)≤
      ((rimIncidentResources ι v\L.biUnion (physicalSampledCandidateSet φ R σ)).card:ℝ):=by
    exact_mod_cast physical_rim_residual_degree_le_uncovered ι _ v
  exact hdegree.trans (hcount.trans (hrow v))
end Oberwolfach
