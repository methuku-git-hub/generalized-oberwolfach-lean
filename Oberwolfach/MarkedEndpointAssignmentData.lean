module

public import Oberwolfach.MarkedEndpointAssignmentIncidences

@[expose] public section

/-! Recover the direction, type and spoke conclusions of the selected
endpoint bijections for the boundary path constructor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U J:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    [Fintype J] [DecidableEq J]
    {A₀ A₁ X₀ X₁:J→Finset V} {Y₀ Y₁:J→Finset U}
    {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}
namespace MarkedEndpointPairing

def assignedIncomingType
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):Bool:=((P i.1).incoming.symm i.2).isRight

def assignedOutgoingType
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):Bool:=((P i.1).outgoing.symm i.2).isRight

theorem assigned_incoming_type
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):assignedIncomingType P i=i.2.isRight:=by
  have hh:=(P i.1).incoming_adj ((P i.1).incoming.symm i.2)
  rw [(P i.1).incoming.apply_symm_apply] at hh
  exact hh.1

theorem assigned_types_compatible
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):¬(assignedIncomingType P i=true∧assignedOutgoingType P i=true):=by
  have hh:=(P i.1).outgoing_adj ((P i.1).outgoing.symm i.2)
  rw [(P i.1).outgoing.apply_symm_apply] at hh
  intro h
  exact hh.1 ⟨h.2,by rw [←assigned_incoming_type P i];exact h.1⟩

theorem assigned_spokes
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):
    H₀ (assignedIncoming P i) (assignedHub P i)∧
      (if assignedOutgoingType P i then HK (assignedOutgoing P i) (assignedHub P i)
        else H₀ (assignedOutgoing P i) (assignedHub P i)):=by
  have hi:=(P i.1).incoming_adj ((P i.1).incoming.symm i.2)
  have ho:=(P i.1).outgoing_adj ((P i.1).outgoing.symm i.2)
  rw [(P i.1).incoming.apply_symm_apply] at hi
  rw [(P i.1).outgoing.apply_symm_apply] at ho
  exact ⟨hi.2,ho.2⟩

theorem assigned_separated
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):¬PermutationClose π b (assignedOutgoing P i) (assignedIncoming P i):=by
  intro h
  exact (P i.1).separated i.2 ((permutationClose_symm π b _ _).mp h)

theorem assigned_label_membership
    (P:∀ j,MarkedEndpointPairing (A₀ j) (A₁ j) (X₀ j) (X₁ j) (Y₀ j) (Y₁ j) H₀ HK π b)
    (i:Σ j,Y₀ j⊕Y₁ j):assignedIncoming P i∈A₀ i.1∪A₁ i.1∧assignedOutgoing P i∈X₀ i.1∪X₁ i.1:=by
  constructor
  · unfold assignedIncoming
    cases (P i.1).incoming.symm i.2 with
    | inl a=>exact Finset.mem_union_left _ a.property
    | inr a=>exact Finset.mem_union_right _ a.property
  · unfold assignedOutgoing
    cases (P i.1).outgoing.symm i.2 with
    | inl a=>exact Finset.mem_union_left _ a.property
    | inr a=>exact Finset.mem_union_right _ a.property

end MarkedEndpointPairing
end Oberwolfach
