module

public import Oberwolfach.LongRawSurvivingMatchingLift
public import Oberwolfach.PhysicalRimResourceResidual

@[expose] public section
/-! The physical rim graph of a matching chosen after deletion is disjoint
from the actual deleted graph, under the original sampled representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_surviving_matching_physical_rims_avoid_deleted_graph
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let q:=survivingCandidateEmbedding R S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))),
    ∀x y,(physicalRimCandidateUnion φ (restrictedResourceSet R (Function.Embedding.subtype (·∈T))) (M.map q)).Adj x y→
      ¬D.Adj x y :=by
  intro R T S q φ M x y hused hD
  obtain ⟨hxy,a,ha,w,hw,hφ⟩:=hused
  have hwR:w.val∈R a.val:=by
    exact (restrictedResourceSet_mem R (Function.Embedding.subtype (·∈T)) a w).mp hw
  have hnot:=long_raw_lifted_matching_avoids_deleted_rims P π d m ℓ raw g j D.edgeFinset M a ha w.val hwR s(x,y)
  apply hnot
  · change typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) w.val)=Sum.inl s(x,y) at hφ
    exact hφ
  · exact SimpleGraph.mem_edgeFinset.mpr hD
end Oberwolfach
