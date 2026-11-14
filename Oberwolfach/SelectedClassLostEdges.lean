module

public import Oberwolfach.ExpandedClassCorrectionArcs
public import Oberwolfach.Neighbourhoods

@[expose] public section
/-! Every selected arc lost when passing to the regular class graph is an
incident edit of the sampled class graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem selected_class_lost_edges_le_edits
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U] [Fintype Γ] [Fintype Color]
    (P S:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) (v:V):
    (Finset.univ.filter (fun w=>
      (rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) v w ∨
       rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) w v) ∧ ¬S.Adj v w)).card≤
      (changed ((longPhysicalStateGraph P σ {0,1,2,3,4}).neighborFinset v) (S.neighborFinset v)).card:=by
  apply Finset.card_le_card
  intro w hw
  have hh:=(Finset.mem_filter.mp hw).2
  have hS₀:(longPhysicalStateGraph P σ {0,1,2,3,4}).Adj v w:=by
    rcases hh.1 with h|h
    · exact (selected_arc_sampled_class P π d σ v w h).1
    · exact (selected_arc_sampled_class P π d σ w v h).1.symm
  simp [changed,SimpleGraph.mem_neighborFinset,hS₀,hh.2]
end Oberwolfach
