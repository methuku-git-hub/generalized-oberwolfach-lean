module

public import Oberwolfach.OrdinaryPlacementColourRecode
public import Oberwolfach.OrdinarySampledSurvivalTarget

@[expose] public section
/-! The recoded free arcs still use sampled physical edges and therefore
survive the original target edit after the same deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def ordinaryPlacementPhysicalRelation {V:Type} [Fintype V] [LinearOrder V]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (ω:Sym2 V→Fin 6×Bool) (x y:V):Prop:=
  rawSelectedPhysicalRelation P π d (fun e=>ordinaryPlacementColourRecode (ω e)) x y

theorem ordinary_placement_recoded_arc_sampled
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (x y:V) (h:ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):
    (longPhysicalStateGraph P σ {0,1,2,3,4}).Adj x y :=by
  have hp:=raw_selected_physical_relation_in_host P π d
    (fun e=>ordinaryPlacementColourRecode (σ (Sum.inl e))) x y h
  have hraw:markedExpandedPhysicalCollapse (ordinaryPlacementColourRecode (σ (Sum.inl s(x,y))))=some (false,orientationBit x y):=by
    have hh:=(markedPhysicalRim_eq_one_iff P π (3*d)
      (fun e=>markedExpandedPhysicalCollapse (ordinaryPlacementColourRecode (σ (Sum.inl e)))) false x y).mp h
    exact hh.2.2
  have hstate:(σ (Sum.inl s(x,y))).1=0 ∨ (σ (Sum.inl s(x,y))).1=4:=by
    rcases hz:σ (Sum.inl s(x,y)) with ⟨state,bit⟩
    fin_cases state <;> simp_all [ordinaryPlacementColourRecode,markedExpandedPhysicalCollapse]
  refine ⟨hp,?_⟩
  rcases hstate with h0|h4
  · simp [h0]
  · simp [h4]

theorem ordinary_placement_recoded_required_target
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P Target Host Del G:SimpleGraph V) (hHost:Host≤P) (hG:G≤Target)
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e):
    let Sample:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let Dfree:=fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
    Sample\Target≤Del→
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Target.Adj x y) ∧
    (∀x y,G.Adj x y→Dstar x y∨Dstar y x) ∧
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Dstar x y→Target.Adj x y) ∧
    (∀x y,Dfree x y→ ordinaryPlacementPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):=by
  intro Sample Dfree Dstar hDel
  have hold:∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Target.Adj x y:=
    (ordinary_sampled_survival_in_target P Target Host Del hHost π d σ hDel).2
  refine ⟨hold,?_,?_,?_,?_⟩
  · intro x y h
    exact Or.inl (Or.inr h)
  · intro x y h
    exact Or.inl h
  · intro x y h
    rcases h with h|h
    · by_contra hn
      exact h.2 (hDel ⟨ordinary_placement_recoded_arc_sampled P π d σ x y h.1,hn⟩)
    · exact hG h
  · intro x y h
    exact h.1
end Oberwolfach
