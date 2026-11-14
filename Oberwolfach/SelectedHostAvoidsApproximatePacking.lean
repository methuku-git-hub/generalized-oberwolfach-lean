module

public import Oberwolfach.RawSelectedPhysicalNeighbourTests
public import Oberwolfach.PhysicalSamplingLayerDisjoint

@[expose] public section
/-! The actual selected-layer directed host avoids any physical packing
contained in the independently categorised approximate layer. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_host_avoids_approximate_packing
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Pack:Finset (Sym2 V)) (hPack:Pack⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    ∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→s(x,y)∉Pack:=by
  intro x y hD hmem
  let raw:RawMarkedOutcome V U Γ Color:=fun e=>rawExpandedMarkedCollapse e (σ e)
  have hR:markedPhysicalRim P π (3*d) (fun e=>raw (Sum.inl e)) false x y=1:=by
    simpa [rawSelectedPhysicalRelation,raw,rawExpandedMarkedCollapse] using hD
  let a:MarkedSampleArc P π (3*d) (fun e=>raw (Sum.inl e)) false:=⟨(x,y),hR⟩
  have hs:s(x,y)∈(longSelectedPhysicalGraph P π d σ).edgeFinset:=by
    simpa only [longSelectedPhysicalGraph,Sum.elim_inl] using
      (markedSampleArcSetGraph_coordinate P π d raw Finset.univ (Sum.inl a)).mpr (Finset.mem_univ _)
  have hA:(longApproximatePhysicalGraph P π d σ).Adj x y:=SimpleGraph.mem_edgeFinset.mp (hPack hmem)
  have hS:(longSelectedPhysicalGraph P π d σ).Adj x y:=SimpleGraph.mem_edgeFinset.mp hs
  have hh:=(disjoint_iff_inf_le.mp (selected_and_approximate_rim_graphs_disjoint P π d σ)) (show (longSelectedPhysicalGraph P π d σ ⊓ longApproximatePhysicalGraph P π d σ).Adj x y from ⟨hS,hA⟩)
  exact hh
end Oberwolfach
