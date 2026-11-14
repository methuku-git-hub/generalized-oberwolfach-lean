module

public import Oberwolfach.OrdinaryOldArcApproximateLayer
public import Oberwolfach.LongApproximateGraphStateInclusion
public import Oberwolfach.LongActualPhysicalGraphsInHost

@[expose] public section
/-! Deleting the sampled edges absent from the edited target suffices for
both selected free arcs and old approximate arcs to survive inside it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampled_survival_in_target
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P Target Host Del:SimpleGraph V) (hHost:Host≤P) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4};
    S₀\Target≤Del→
    (∀x y,rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y→¬Del.Adj x y→Target.Adj x y) ∧
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Target.Adj x y):=by
  intro S₀ hDel
  have hsurvive:∀x y,S₀.Adj x y→¬Del.Adj x y→Target.Adj x y:=by
    intro x y hs hn
    by_contra ht
    exact hn (hDel ⟨hs,ht⟩)
  constructor
  · intro x y hsel hnot
    have hp:=raw_selected_physical_relation_in_host P π d (fun e=>σ (Sum.inl e)) x y hsel
    have hraw:markedExpandedPhysicalCollapse (σ (Sum.inl s(x,y)))=some (false,orientationBit x y):=by
      have hh:=(markedPhysicalRim_eq_one_iff P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x y).mp hsel
      exact hh.2.2
    have hzero:(σ (Sum.inl s(x,y))).1=0:=by
      rcases hz:σ (Sum.inl s(x,y)) with ⟨state,bit⟩
      fin_cases state <;> simp_all [markedExpandedPhysicalCollapse]
    have hs:S₀.Adj x y:=by
      exact ⟨hp,by simp [hzero]⟩
    exact hsurvive x y hs hnot
  · intro x y harc
    have he:=raw_mixed_deleted_arc_in_approximate_layer P Host Del hHost π d σ x y harc
    have ha:(longApproximatePhysicalGraph P π d σ).Adj x y:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    have h23:=long_approximate_graph_in_state_graph P π d σ ha
    have hsub:({2,3}:Finset (Fin 6))⊆{0,1,2,3,4}:=by decide
    have hs:S₀.Adj x y:=⟨h23.1,hsub h23.2⟩
    have hn:¬Del.Adj x y:=(raw_mixed_deleted_arc_host Host Del π d
      (fun e=>rawExpandedApproximateCollapse e (σ e)) x y harc).2
    exact hsurvive x y hs hn
end Oberwolfach
