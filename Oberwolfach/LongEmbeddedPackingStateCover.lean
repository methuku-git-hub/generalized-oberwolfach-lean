module

public import Oberwolfach.LongApproximateGraphStateInclusion

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]

theorem long_embedded_packing_state_cover
    (G Old New Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (hOld:Old.edgeFinset⊆(longApproximatePhysicalGraph G π d ω).edgeFinset)
    (hSmall:Small≤Old⊔New):
    Small≤longPhysicalStateGraph G ω {2,3}⊔New:=by
  have hLayer:Old≤longApproximatePhysicalGraph G π d ω:=by
    intro x y h
    have he:s(x,y)∈Old.edgeFinset:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using h
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hOld he
  exact hSmall.trans (sup_le_sup (hLayer.trans (long_approximate_graph_in_state_graph G π d ω)) le_rfl)

theorem long_embedded_physical_packing_state_cover
    (G New Small:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (ω:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Pack:Finset (Sym2 V)) (hPack:Pack⊆(longApproximatePhysicalGraph G π d ω).edgeFinset)
    (hSmall:Small≤SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))⊔New):
    Small≤longPhysicalStateGraph G ω {2,3}⊔New:=by
  have hOld:SimpleGraph.fromEdgeSet (↑Pack:Set (Sym2 V))≤longApproximatePhysicalGraph G π d ω:=by
    intro x y h
    have he:s(x,y)∈Pack:=(SimpleGraph.fromEdgeSet_adj _).mp h |>.1
    have hh:=hPack he
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
  exact hSmall.trans (sup_le_sup (hOld.trans (long_approximate_graph_in_state_graph G π d ω)) le_rfl)

end Oberwolfach
