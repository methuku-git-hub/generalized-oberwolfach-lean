module

public import Oberwolfach.OrdinarySelectedAddedDirectedTarget
public import Oberwolfach.OrdinaryLostEdgesEditDegree

@[expose] public section
/-! The sparse deletion and directed relations for the actual edited sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_canonical_edited_target_relations
    {V U Γ Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Γ] [Fintype Color]
    (P Target Host:SimpleGraph V) (hTarget:Target≤P) (hHost:Host≤P)
    (π:Equiv.Perm V) (d:ℕ)
    (σ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)
    (b:ℝ):
    let S₀:=longPhysicalStateGraph P σ {0,1,2,3,4}
    let G:=Target\S₀
    let Del:=S₀\Target
    let Dfree:=fun x y=>rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y ∧ ¬Del.Adj x y
    let Dstar:=fun x y=>Dfree x y ∨ G.Adj x y;
    (∀x,((Finset.univ.filter (fun y=>Xor (Target.Adj x y) (S₀.Adj x y))).card:ℝ)≤b)→
    (∀x,(Del.degree x:ℝ)≤b) ∧ (∀x,(G.degree x:ℝ)≤b) ∧
    (∀x y,rawMixedPhysicalArc Host π d
      (rawMarkedDeleteRims (fun e=>rawExpandedApproximateCollapse e (σ e)) Del.edgeFinset) x y→Target.Adj x y) ∧
    (∀x y,G.Adj x y→Dstar x y∨Dstar y x) ∧
    (∀x y,Dfree x y→Dstar x y) ∧
    (∀x y,Dstar x y→Target.Adj x y) ∧
    (∀x y,Dfree x y→ rawSelectedPhysicalRelation P π d (fun e=>σ (Sum.inl e)) x y):=by
  intro S₀ G Del Dfree Dstar hedit
  have hlost:=lost_graph_degree_le_symmetric_edit Target S₀ b hedit
  have hadded:=added_graph_degree_le_symmetric_edit Target S₀ b hedit
  have hrel:=ordinary_selected_added_directed_target P Target Host Del hTarget hHost π d σ (by exact le_rfl)
  refine ⟨hlost,hadded,?_,hrel.2⟩
  intro x y h
  apply hrel.1 x y
  convert h using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
