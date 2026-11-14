module

public import Oberwolfach.OrdinaryPlacementRecodeTarget
public import Oberwolfach.OrdinaryOldEdgesApproximateLayer
public import Oberwolfach.LongApproximateGraphStateInclusion

@[expose] public section
/-! Recoded free arcs use states zero or four, so they do not meet the
matching's old edges in approximate states two or three. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_placement_recoded_avoids_approximate_edges
    {V U Γ Color I:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color] (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (Old:I→Finset (Sym2 V)) (hOld:∀i,Old i⊆(longApproximatePhysicalGraph P π d σ).edgeFinset)
    (Dfree:V→V→Prop) (hfree:∀x y,Dfree x y→ ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):
    ∀i x y,Dfree x y→s(x,y)∉Old i:=by
  intro i x y hh he
  have ha:(longApproximatePhysicalGraph P π d σ).Adj x y:=by
    simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hOld i he
  have h23:=long_approximate_graph_in_state_graph P π d σ ha
  have hsel:=hfree x y hh
  have hraw:markedExpandedPhysicalCollapse (ordinaryPlacementColourRecode (σ (Sum.inl s(x,y))))=some (false,orientationBit x y):=by
    have ht:=(markedPhysicalRim_eq_one_iff P π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (ordinaryPlacementColourRecode (σ (Sum.inl e)))) false x y).mp hsel
    exact ht.2.2
  have hstate:(σ (Sum.inl s(x,y))).1=0 ∨ (σ (Sum.inl s(x,y))).1=4:=by
    rcases hz:σ (Sum.inl s(x,y)) with ⟨state,bit⟩
    fin_cases state <;> simp_all [ordinaryPlacementColourRecode,markedExpandedPhysicalCollapse]
  change P.Adj x y ∧ (σ (Sum.inl s(x,y))).1∈({2,3}:Finset (Fin 6)) at h23
  simp only [Finset.mem_insert,Finset.mem_singleton] at h23
  rcases h23.2 with h2|h3 <;> rcases hstate with h0|h4 <;> simp_all
end Oberwolfach
