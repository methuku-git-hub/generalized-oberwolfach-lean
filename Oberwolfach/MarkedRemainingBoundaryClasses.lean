module

public import Oberwolfach.MarkedSampleBoundaryAfterPacking
public import Oberwolfach.MarkedSampleDeletedArcs
public import Oberwolfach.MarkedNeighbourhoodPhysicalDeletion

@[expose] public section

/-! The endpoint and spoke classes of the actual deleted sample agree
exactly with the corresponding classes in the remaining boundary graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_remaining_endpoint_class
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U) (hX:∀ x,π x∈X↔x∈X)
    (DR:SimpleGraph V) (HD:V→U→Prop) (mark incoming:Bool) (x:V) (hx:x∉X):
    let G:=ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ Finset.univ)
      (fun x u=>H false x u∨H true x u) X Z
    let C:=ordinaryPhysicalGraph DR HD;
    markedEndpointLabels P π d X (mark,incoming,x) (rawMarkedDeleteRims σ DR.edgeFinset)=
      (markedEndpointLabels P π d X (mark,incoming,x) σ).filter
        (fun v=>markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)∈(G\C).edgeSet):=by
  intro G C
  ext v
  have hg: v∈markedEndpointLabels P π d X (mark,incoming,x) σ→
      markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)∈G.edgeSet:=
    marked_sample_endpoint_coin_mem_boundary P π d σ H X Z hX mark incoming x hx v
  have he:v∈markedEndpointLabels P π d X (mark,incoming,x) (rawMarkedDeleteRims σ DR.edgeFinset)↔
      v∈markedEndpointLabels P π d X (mark,incoming,x) σ∧
      s((if incoming then v else x),if mark then π (if incoming then x else v) else (if incoming then x else v))∉DR.edgeFinset:=by
    rw [marked_endpoint_labels_actual,marked_endpoint_labels_actual]
    simp only [Finset.mem_filter,markedPhysicalRim_delete_iff]
    tauto
  rw [he,Finset.mem_filter]
  have hc:markedBoundaryEndpointCoin π mark incoming x (Sum.inl v)∈C.edgeSet↔
      s((if incoming then v else x),if mark then π (if incoming then x else v) else (if incoming then x else v))∈DR.edgeFinset:=by
    rw [marked_boundary_endpoint_rim_coin]
    cases mark <;> cases incoming <;>
      simp only [Bool.false_eq_true,ite_false,ite_true,SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet,C,ordinaryPhysicalGraph]
  rw [SimpleGraph.edgeSet_sdiff]
  simp only [Set.mem_diff,hc]
  tauto

theorem marked_remaining_spoke_class
    (Q:SimpleGraph V) (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (b:Bool) (x:V) (hx:x∉X):
    Z.filter (markedDeletePhysicalSpokes H C b x)=
      (Z.filter (H b x)).filter (fun u=>(ordinaryBoundaryGraph Q
        (fun x u=>H false x u∨H true x u) X Z\C).Adj (Sum.inl x) (Sum.inr u)):=by
  ext u
  have hb:H b x u→H false x u∨H true x u:=by cases b;exact Or.inl;exact Or.inr
  simp only [Finset.mem_filter,markedDeletePhysicalSpokes,SimpleGraph.sdiff_adj,
    ordinaryBoundaryGraph_adj,ordinaryPhysicalGraph,ordinaryInnerVertices_left,ordinaryInnerVertices_right,hx]
  tauto

theorem marked_remaining_spoke_column
    (Q:SimpleGraph V) (H:Bool→V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (u:U) (hu:u∉Z):
    X.filter (fun x=>(H false x u∨H true x u)∧¬C.Adj (Sum.inl x) (Sum.inr u))=
      (X.filter (fun x=>H false x u∨H true x u)).filter (fun x=>(ordinaryBoundaryGraph Q
        (fun x u=>H false x u∨H true x u) X Z\C).Adj (Sum.inl x) (Sum.inr u)):=by
  ext x
  simp only [Finset.mem_filter,SimpleGraph.sdiff_adj,ordinaryBoundaryGraph_adj,ordinaryPhysicalGraph,
    ordinaryInnerVertices_left,ordinaryInnerVertices_right,hu]
  tauto
end Oberwolfach
