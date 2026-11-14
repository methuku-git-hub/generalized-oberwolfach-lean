module

public import Oberwolfach.PhysicalResidualAfterDeletion
public import Oberwolfach.LongRawSurvivingResourceState

@[expose] public section
/-! Specialization to the actual raw sample and physical deletion graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_physical_residual_after_rim_deletion
    (P D:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d:ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let T:=bernoulliVertexSet (longRawHubState P π d raw g j)
    let S:=longRawSurvivingResources P π d raw g j D.edgeFinset
    let f:=survivingResourceEmbedding S T (long_raw_surviving_resources_subset P π d raw g j D.edgeFinset)
    let φ:=markedRawSampledPhysicalEmbedding P π d raw g j
    ∀covered:Finset S,
      physicalRimResidualGraph φ (covered.map f) ≤
        physicalRimResidualGraph (f.trans φ) covered ⊔ D :=by
  intro T S f φ covered
  apply physical_rim_residual_after_deletion φ f D covered
  intro w hw x y hφ hxy
  change s(x,y)∈D.edgeSet
  apply SimpleGraph.mem_edgeFinset.mp
  by_contra he
  have hs:w.val∈S:=by
    apply Finset.mem_filter.mpr
    refine ⟨w.property,?_⟩
    change (match typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) w.val) with
      | Sum.inl edge => edge∉D.edgeFinset
      | Sum.inr _ => True)
    change typedResourcePhysical π ((markedResourceTypeEquiv (V:=Fin n) (U:=U)) w.val)=Sum.inl s(x,y) at hφ
    rw [hφ]
    exact he
  exact hw ⟨w.val,hs⟩ (Subtype.ext rfl)
end Oberwolfach
