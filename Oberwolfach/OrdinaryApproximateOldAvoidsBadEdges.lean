module

public import Oberwolfach.OrdinaryOldEdgesApproximateLayer
public import Oberwolfach.LongApproximateGraphStateInclusion

@[expose] public section
/-! The old approximate layer lies in the sampled physical graph, so it is
disjoint from every edge newly added relative to that graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_approximate_old_avoids_added_edges
    {V U Γ Color I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Old:I→Finset (Sym2 V)) (hOld:∀i,Old i⊆(longApproximatePhysicalGraph P π d σ).edgeFinset):
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4};
    ∀i,Disjoint (Old i) (S\S₀).edgeFinset:=by
  intro S₀ i
  have hsub:({2,3}:Finset (Fin 6))⊆{0,1,2,3,4}:=by decide
  have hgraph:longApproximatePhysicalGraph P π d σ≤S₀:=by
    intro x y hxy
    have hh:=long_approximate_graph_in_state_graph P π d σ hxy
    exact ⟨hh.1,hsub hh.2⟩
  have hEdges:(longApproximatePhysicalGraph P π d σ).edgeFinset⊆S₀.edgeFinset:=SimpleGraph.edgeFinset_mono hgraph
  apply Finset.disjoint_left.mpr
  intro e heOld heBad
  have heS₀:=hEdges (hOld i heOld)
  rw [SimpleGraph.edgeFinset_sdiff] at heBad
  exact (Finset.mem_sdiff.mp heBad).2 heS₀
end Oberwolfach
