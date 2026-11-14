module

public import Oberwolfach.MarkedRemainingBoundaryClasses
public import Oberwolfach.MarkedBoundaryNeighbourhoods

@[expose] public section

/-! The remaining endpoint labels belong to the actual boundary support,
with their original direction, type and physical coin. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Gamma Color:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    [Fintype Gamma] [Fintype Color]

theorem marked_endpoint_class_boundary_support
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (X:Finset V) (τ:Sym2 (V⊕U)→Bool) (mark incoming:Bool) (x:V):
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true;
    ((markedEndpointLabels P π d X (mark,incoming,x) σ).filter
      (fun v=>τ (markedBoundaryEndpointCoin π mark incoming x (Sum.inl v))=true))⊆
    markedBoundaryRimNeighbours (fun e:E=>e.val.1) (fun e:E=>e.val.2)
      (fun e:K=>e.val.1) (fun e:K=>e.val.2) π X τ x:=by
  intro E K v hv
  obtain ⟨hv,hcoin⟩:=Finset.mem_filter.mp hv
  rw [marked_endpoint_labels_actual] at hv
  obtain ⟨hvX,hv⟩:=Finset.mem_filter.mp hv
  apply Finset.mem_filter.mpr
  refine ⟨hvX,?_⟩
  rw [marked_boundary_endpoint_rim_coin] at hcoin
  cases mark <;> cases incoming
  all_goals simp only [Bool.false_eq_true,ite_false,ite_true] at hv hcoin
  · refine ⟨Sum.inl ⟨(x,v),hv⟩,Or.inl ⟨rfl,rfl⟩,?_⟩
    exact hcoin
  · refine ⟨Sum.inl ⟨(v,x),hv⟩,Or.inr ⟨rfl,rfl⟩,?_⟩
    exact hcoin
  · refine ⟨Sum.inr ⟨(x,v),hv⟩,Or.inl ⟨rfl,rfl⟩,?_⟩
    exact hcoin
  · refine ⟨Sum.inr ⟨(v,x),hv⟩,Or.inr ⟨rfl,rfl⟩,?_⟩
    exact hcoin

theorem marked_deleted_endpoint_subset
    (P:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawMarkedOutcome V U Gamma Color)
    (X:Finset V) (DR:Finset (Sym2 V)) (mark incoming:Bool) (x:V):
    markedEndpointLabels P π d X (mark,incoming,x) (rawMarkedDeleteRims σ DR)⊆
      markedEndpointLabels P π d X (mark,incoming,x) σ:=by
  intro v hv
  rw [marked_endpoint_labels_actual] at hv ⊢
  obtain ⟨hvX,hv⟩:=Finset.mem_filter.mp hv
  exact Finset.mem_filter.mpr ⟨hvX,((markedPhysicalRim_delete_iff P π d σ DR mark _ _).mp hv).1⟩

theorem marked_spoke_class_boundary_support
    (H:Bool→V→U→Prop) (Z:Finset U) (τ:Sym2 (V⊕U)→Bool) (b:Bool) (x:V):
    ((Z.filter (H b x)).filter (fun u=>τ s(Sum.inl x,Sum.inr u)=true))⊆
      markedBoundarySpokeHubs (H false) (H true) Z τ x:=by
  intro u hu
  obtain ⟨⟨hu,hH⟩,hτ⟩:=Finset.mem_filter.mp hu |>.imp (fun h=>Finset.mem_filter.mp h) id
  apply Finset.mem_filter.mpr
  refine ⟨hu,?_,hτ⟩
  cases b
  · exact Or.inl hH
  · exact Or.inr hH
end Oberwolfach
