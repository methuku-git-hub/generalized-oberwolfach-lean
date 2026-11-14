module

public import Oberwolfach.RawLayerPhysicalResourceDisjoint
public import Oberwolfach.MarkedRawSampledPhysicalEmbedding

@[expose] public section
/-! Every active raw typed approximate resource maps to a physical resource
of the original approximate layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color]

theorem raw_sampled_physical_embedding_in_approximate_layer
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (g:Γ) (j:Color):
    let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedApproximateCollapse e (σ e)
    ∀w,markedRawSampledPhysicalEmbedding P π d raw g j w∈
      wheelLayerPhysicalResources (longApproximatePhysicalGraph P π d σ)
        (rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j) :=by
  intro raw w
  have ha:typedMarkedResourceState (rawMarkedPairRims P π d raw) (rawMarkedPairSpokes π d raw g j) w.val=true:=
    (mem_bernoulliVertexSet _ _).mp w.property
  rcases w with ⟨z,hz⟩
  cases z with
  | inl e=>
    cases e with
    | inl xy=>
      have hR:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) false xy.1 xy.2=1:=by
        simpa [typedMarkedResourceState,rawMarkedPairRims] using ha
      let a:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨xy,hR⟩
      have he:s(xy.1,xy.2)∈(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
        simpa only [longApproximatePhysicalGraph,Sum.elim_inl] using
          (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl a)).mpr (Finset.mem_univ _)
      simp only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image]
      left
      refine ⟨s(xy.1,xy.2),he,?_⟩
      rfl
    | inr xy=>
      have hR:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) true xy.1 xy.2=1:=by
        simpa [typedMarkedResourceState,rawMarkedPairRims] using ha
      let a:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) true:=⟨xy,hR⟩
      have he:s(xy.1,π xy.2)∈(longApproximatePhysicalGraph P π d σ).edgeFinset:=by
        simpa only [longApproximatePhysicalGraph,Sum.elim_inr] using
          (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inr a)).mpr (Finset.mem_univ _)
      simp only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image]
      left
      refine ⟨s(xy.1,π xy.2),he,?_⟩
      rfl
  | inr z=>
    rcases z with ⟨b,v,u⟩
    have hS:rawMarkedSpokes π d (fun e=>σ (Sum.inr e)) g j b v u:=by
      simpa [typedMarkedResourceState,rawMarkedPairSpokes,raw,rawExpandedApproximateCollapse] using ha
    simp only [wheelLayerPhysicalResources,Finset.mem_union,Finset.mem_image]
    right
    refine ⟨(v,u),Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨b,hS⟩⟩,?_⟩
    rfl
end Oberwolfach
