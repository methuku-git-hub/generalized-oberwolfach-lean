module

public import Oberwolfach.OrdinaryPhysicalMatchingRimResidual
public import Oberwolfach.OrdinaryRemainderReferenceEdits

@[expose] public section
/-! Transfer the matching's row control to the actual complement once its
matched physical rims have been embedded, allowing an explicit exceptional
graph for deleted or geometrically ineligible sampled edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_uncovered_rim_degree_from_physical_matching
    {V U A C:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype C]
    [DecidableEq V] [DecidableEq U] [DecidableEq A] [DecidableEq C]
    (φ:A→Sym2 V⊕(V×U)) (R:C→Finset A) (σ:A→Bool)
    (L:Finset (PhysicalSampledCandidate R σ)) (Sample Reference Embedded Except:SimpleGraph V)
    (κ δ:ℝ)
    (hrow:∀v,(((physicalSampledRow φ σ (ordinaryPhysicalRow (.inl v)))\
      L.biUnion (physicalSampledCandidateSet φ R σ)).card:ℝ)≤κ)
    (hExcept:∀v,(Except.degree v:ℝ)≤δ):
    let ι:PhysicalSampledActive φ σ↪Sym2 V⊕(V×U):=Function.Embedding.subtype _
    (Sample\Reference≤physicalRimResidualGraph ι ∅⊔Except)→
    (physicalRimCoveredGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))≤Embedded)→
    ∀v,(((Sample\Reference)\Embedded).degree v:ℝ)≤κ+δ:=by
  intro ι hactive hpacked v
  have hsub:(Sample\Reference)\Embedded≤
      physicalRimResidualGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))⊔Except:=by
    intro x y hxy
    rcases hactive hxy.1 with ha|he
    · left
      refine ⟨ha.1,?_⟩
      obtain ⟨z,_,hz⟩:=ha.2
      refine ⟨z,?_,hz⟩
      intro hcov
      exact hxy.2 (hpacked ⟨ha.1,z,hcov,hz⟩)
    · exact Or.inr he
  have hdeg:((((Sample\Reference)\Embedded).degree v):ℝ)≤
      ((physicalRimResidualGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))⊔Except).degree v:ℝ):=by
    exact_mod_cast SimpleGraph.degree_le_of_le hsub
  have hsum:(((physicalRimResidualGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))⊔Except).degree v):ℝ)≤
      ((physicalRimResidualGraph ι (L.biUnion (physicalSampledCandidateSet φ R σ))).degree v:ℝ)+Except.degree v:=by
    exact_mod_cast graph_degree_sup_le _ _ v
  have hr:=ordinary_physical_matching_rim_residual_degree φ R σ L κ hrow v
  linarith [hExcept v]
end Oberwolfach
