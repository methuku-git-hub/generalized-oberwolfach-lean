module

public import Oberwolfach.MarkedSampleDeletedArcs
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion
public import Oberwolfach.MarkedPackingUnions

@[expose] public section

/-! Return wheels in the current physically deleted sample to their
original sampled host. The tuple, hub, occurrence types, directions and
physical resources are unchanged. Both deleted rims and spokes are avoided. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

abbrev MarkedPhysicalDeletedSampleWheel
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (H:Bool→V→U→Prop):=
  MarkedWheel
    (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
    (fun e:MarkedSampleArc P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
    m π (3*d) (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true)

def markedPhysicalDeletedSampleWheelLift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (H:Bool→V→U→Prop)
    (W:MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H):
    MarkedWheel
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
      (fun e:MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
      m π (3*d) (H false) (H true):=
  let W':=markedSampleDeletedWheelToOriginal P π d m σ DR.edgeFinset
    (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) W
  ⟨W'.1,⟨W'.2.val,W'.2.property.1.1,fun i=>(W'.2.property.2 i).1⟩⟩

theorem markedPhysicalDeletedSampleWheelLift_resources
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (H:Bool→V→U→Prop)
    (W:MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H):
    markedWheelPhysicalResources (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H W)=
      markedWheelPhysicalResources W:=by
  exact markedSampleDeletedWheelToOriginal_resources P π d m σ DR.edgeFinset
    (markedDeletePhysicalSpokes H DS false) (markedDeletePhysicalSpokes H DS true) W

theorem markedPhysicalDeletedSampleWheel_avoids
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (H:Bool→V→U→Prop)
    (W:MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H):
    (∀ x y,({x,y}:Finset V)∈markedCyclePhysicalEdges _ _ _ _ m π (3*d) W.1→¬DR.Adj x y) ∧
    (∀ x u,Sum.inr (x,u)∈markedWheelPhysicalResources W→¬DS.Adj (Sum.inl x) (Sum.inr u)):=by
  refine ⟨?_,?_⟩
  · intro x y he hxy
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
    simp only [Function.comp_apply] at hi
    generalize markedCycleTypedEdge _ _ _ _ m π (3*d) W.1 i=a at hi
    cases a with
    | inl a=>
      have hn:=((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset false _ _).mp a.property).2
      have hd:¬DR.Adj a.val.1 a.val.2:=by
        simpa only [Bool.false_eq_true,ite_false,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hn
      exact hd (graph_adj_of_physical_pair_eq DR _ _ x y hi hxy)
    | inr a=>
      have hn:=((markedPhysicalRim_delete_iff P π d σ DR.edgeFinset true _ _).mp a.property).2
      have hd:¬DR.Adj a.val.1 (π a.val.2):=by
        simpa only [ite_true,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hn
      exact hd (graph_adj_of_physical_pair_eq DR _ _ x y hi hxy)
  · intro x u he
    rcases markedWheelPhysicalResources_spoke_present W x u he with h|h
    · exact h.2
    · exact h.2

theorem markedPhysicalDeletedSamplePacking_lift
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (σ:RawMarkedOutcome V U Γ Color)
    (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)) (H:Bool→V→U→Prop)
    (M:Finset (MarkedPhysicalDeletedSampleWheel P π d m σ DR DS H))
    (hM:∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)):
    let M':=M.image (markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H)
    M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources ∧
    (∀ W∈M',∀ Z∈M',W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
    Disjoint (markedPackingRimGraph M') DR ∧
    (∀ x u,markedPackingSpokes M' x u→¬DS.Adj (Sum.inl x) (Sum.inr u)):=by
  let f:=markedPhysicalDeletedSampleWheelLift P π d m σ DR DS H
  have hr:∀ W,markedWheelPhysicalResources (f W)=markedWheelPhysicalResources W:=
    markedPhysicalDeletedSampleWheelLift_resources P π d m σ DR DS H
  have hu:(M.image f).biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources:=by
    rw [Finset.image_biUnion]
    simp only [hr]
  refine ⟨hu,?_,?_,?_⟩
  · intro W hW Z hZ hne
    obtain ⟨X,hX,rfl⟩:=Finset.mem_image.mp hW
    obtain ⟨Y,hY,rfl⟩:=Finset.mem_image.mp hZ
    rw [hr,hr]
    exact hM X hX Y hY (fun he=>hne (congrArg f he))
  · apply disjoint_iff_inf_le.mpr
    intro x y hboth
    obtain ⟨hxy,hD⟩:=hboth
    apply False.elim
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp hxy.2
    obtain ⟨W,hW,rfl⟩:=Finset.mem_image.mp hW
    have he':Sum.inl ({x,y}:Finset V)∈markedWheelPhysicalResources W:=by
      rw [←hr]
      exact (markedWheelPhysicalResources_rim (f W) _).mpr he
    exact (markedPhysicalDeletedSampleWheel_avoids P π d m σ DR DS H W).1 x y
      ((markedWheelPhysicalResources_rim W _).mp he') hD
  · intro x u hxu
    obtain ⟨W,hW,hw,hrows⟩:=hxu
    have he:Sum.inr (x,u)∈markedWheelPhysicalResources W:=
      (markedWheelPhysicalResources_spoke W x u).mpr ⟨hw,hrows⟩
    obtain ⟨W,hW,rfl⟩:=Finset.mem_image.mp hW
    rw [hr] at he
    exact (markedPhysicalDeletedSampleWheel_avoids P π d m σ DR DS H W).2 x u he

end Oberwolfach
