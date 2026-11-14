module

public import Oberwolfach.SelectedClassLostEdges
public import Oberwolfach.SelectedCommonEventRoutingPaths

@[expose] public section
/-! The actual two-path tests and regularisation edit bound imply the routing
path supply; no independent lost-edge hypothesis is needed. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_routing_paths_from_class_edits
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (p err b β:ℝ) (hb:0≤b)
    (hedit:∀v,((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ)≤b)
    (htest:∀x y,x≠y→((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err≤
      ((Finset.univ.filter (fun z=>
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false x z ∧
        0<markedPhysicalRim P π (3*d) (fun e=>markedExpandedPhysicalCollapse (σ (Sum.inl e))) false z y)).card:ℝ))
    (hmargin:∀x y,x≠y→β*Fintype.card V+2*b≤
      ((P.neighborFinset x∩P.neighborFinset y).card:ℝ)*p^2-err):
    ∀x y,x≠y→β*Fintype.card V≤
      ((Finset.univ.filter (fun z=>0<sampledOrientation S (fun e=>(σ (Sum.inl e)).2) x z ∧
        0<sampledOrientation S (fun e=>(σ (Sum.inl e)).2) z y ∧ S.Adj x z ∧ S.Adj z y)).card:ℝ):=by
  apply selected_common_event_routing_paths P S π d (fun e=>σ (Sum.inl e)) p err b β hb ?_ htest hmargin
  intro v
  have hh:=selected_class_lost_edges_le_edits P S π d σ v
  have hh':((Finset.univ.filter (fun w=>
      (rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) v w ∨
       rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) w v) ∧ ¬S.Adj v w)).card:ℝ)≤
      ((changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:ℝ):=by exact_mod_cast hh
  exact hh'.trans (hedit v)
end Oberwolfach
