module

public import Oberwolfach.MarkedAttachmentEndpointOwnership

@[expose] public section

/-! Four ordinary attachment requests at each rim-wheel hub. They are
indexed by the inverse slot assignment, so they belong to the vertex
wheels using this hub. The derangement excludes the hub's own rim path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V A:Type} [DecidableEq V] {src dst:A→V}

 def markedIncomingAssignedSlot (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v)) (e:A):
    Σ v,DirectedIncidence src dst v:=⟨dst e,(τ (dst e)).symm (Sum.inl ⟨e,rfl⟩)⟩

 def markedOutgoingAssignedSlot (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v)) (e:A):
    Σ v,DirectedIncidence src dst v:=⟨src e,(τ (src e)).symm (Sum.inr ⟨e,rfl⟩)⟩

 def markedRimHubAttachmentRows (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (first last:(Σ v,DirectedIncidence src dst v)→V) (e:A):Finset V:=
    {first (markedIncomingAssignedSlot τ e),last (markedIncomingAssignedSlot τ e),
      first (markedOutgoingAssignedSlot τ e),last (markedOutgoingAssignedSlot τ e)}

 theorem markedRimHubAttachmentRows_card (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (first last:(Σ v,DirectedIncidence src dst v)→V) (e:A):
    (markedRimHubAttachmentRows τ first last e).card≤4:=by
  dsimp [markedRimHubAttachmentRows]
  have h₁:=Finset.card_insert_le (first (markedIncomingAssignedSlot τ e))
    ({last (markedIncomingAssignedSlot τ e),first (markedOutgoingAssignedSlot τ e),last (markedOutgoingAssignedSlot τ e)}:Finset V)
  have h₂:=Finset.card_insert_le (last (markedIncomingAssignedSlot τ e))
    ({first (markedOutgoingAssignedSlot τ e),last (markedOutgoingAssignedSlot τ e)}:Finset V)
  have h₃:=Finset.card_insert_le (first (markedOutgoingAssignedSlot τ e)) ({last (markedOutgoingAssignedSlot τ e)}:Finset V)
  simp only [Finset.card_singleton] at h₃
  omega

 theorem marked_assigned_attachment_rows_avoid_rim_path
    (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v)) (hτ:∀ v i,τ v i≠i)
    (hloop:∀ e,dst e≠src e) (first last:(Σ v,DirectedIncidence src dst v)→V)
    (P:A→Finset V)
    (hown:∀ z:Σ v,DirectedIncidence src dst v,∀ e,first z∈P e∨last z∈P e→e=directedIncidenceEdge z.2):
    ∀ e,Disjoint (markedRimHubAttachmentRows τ first last e) (P e):=by
  have avoid (e:A) (z:Σ v,DirectedIncidence src dst v)
      (hz:directedIncidenceEdge (τ z.1 z.2)=e):first z∉P e∧last z∉P e:=by
    have hne:=directed_incidence_assignment_avoids_own_edge hloop z.1 (τ z.1) (hτ z.1) z.2
    constructor
    · intro hh;exact hne (hz.trans (hown z e (Or.inl hh)))
    · intro hh;exact hne (hz.trans (hown z e (Or.inr hh)))
  intro e
  have hin:=avoid e (markedIncomingAssignedSlot τ e) (by simp [markedIncomingAssignedSlot,directedIncidenceEdge])
  have hout:=avoid e (markedOutgoingAssignedSlot τ e) (by simp [markedOutgoingAssignedSlot,directedIncidenceEdge])
  apply Finset.disjoint_left.mpr
  intro v hv hp
  simp only [markedRimHubAttachmentRows,Finset.mem_insert,Finset.mem_singleton] at hv
  rcases hv with rfl|rfl|rfl|rfl
  · exact hin.1 hp
  · exact hin.2 hp
  · exact hout.1 hp
  · exact hout.2 hp

 theorem marked_assigned_slot_rows_include
    (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (first last:(Σ v,DirectedIncidence src dst v)→V) (z:Σ v,DirectedIncidence src dst v):
    first z∈markedRimHubAttachmentRows τ first last (directedIncidenceEdge (τ z.1 z.2))∧
      last z∈markedRimHubAttachmentRows τ first last (directedIncidenceEdge (τ z.1 z.2)):=by
  rcases z with ⟨v,z⟩
  have hh:τ v z=τ v z:=rfl
  generalize he:τ v z=q at hh ⊢
  cases q with
  | inl q=>
    rcases q with ⟨e,hv⟩
    subst v
    have hslot:markedIncomingAssignedSlot τ e=⟨dst e,z⟩:=by
      dsimp only [markedIncomingAssignedSlot]
      have hz:(τ (dst e)).symm (Sum.inl ⟨e,rfl⟩)=z:=by
        rw [←he,Equiv.symm_apply_apply]
      rw [hz]
    simp only [directedIncidenceEdge,Sum.elim_inl,markedRimHubAttachmentRows,hslot,Finset.mem_insert,Finset.mem_singleton]
    tauto
  | inr q=>
    rcases q with ⟨e,hv⟩
    subst v
    have hslot:markedOutgoingAssignedSlot τ e=⟨src e,z⟩:=by
      dsimp only [markedOutgoingAssignedSlot]
      have hz:(τ (src e)).symm (Sum.inr ⟨e,rfl⟩)=z:=by
        rw [←he,Equiv.symm_apply_apply]
      rw [hz]
    simp only [directedIncidenceEdge,Sum.elim_inr,markedRimHubAttachmentRows,hslot,Finset.mem_insert,Finset.mem_singleton]
    tauto

end Oberwolfach
