module

public import Oberwolfach.OrdinaryAttachmentWheels
public import Oberwolfach.OrdinaryOldVertexLift
public import Oberwolfach.OrdinaryGraphPairUnions

@[expose] public section

/-! Attachments are the disjoint union of the original graph pair and
an actual wheel union. Their balance and divisibility follow without an
assumption that the original graph already decomposes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I W : Type} [Fintype V] [Fintype U] [Fintype I] [Fintype W]
    [DecidableEq V] [DecidableEq U] [DecidableEq I] [DecidableEq W] {r : ℕ}

theorem ordinaryAttachment_rim_union (G : SimpleGraph V) (C : SimpleGraph W) (z : W) (ρ : I → V) :
    ordinaryAttachmentRim G C z ρ=ordinaryOldRim G ⊔ ordinaryAttachmentRim ⊥ C z ρ := by
  ext a b
  rcases a with a|⟨i,w⟩ <;> rcases b with b|⟨j,w'⟩
  all_goals simp [SimpleGraph.sup_adj,ordinaryAttachmentRim,ordinaryOldRim_old_old,
    ordinaryOldRim_old_private,ordinaryOldRim_private_any]

theorem ordinaryAttachment_spoke_union (H : V → U → Prop) (z : W) (ρ : I → V) :
    ordinaryAttachmentSpokes H z ρ=(fun a b => ordinaryOldSpokes H a b ∨
      ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ a b) := by
  funext a b
  cases a <;> cases b <;> simp [ordinaryAttachmentSpokes,ordinaryOldSpokes]

theorem ordinaryAttachment_rim_disjoint (G : SimpleGraph V) (C : SimpleGraph W) (z : W) (ρ : I → V) :
    Disjoint (ordinaryOldRim G) (ordinaryAttachmentRim ⊥ C z ρ) := by
  apply disjoint_iff_inf_le.mpr
  intro a b h
  rcases a with a|p
  · cases b with
    | inl b => exact h.2.elim
    | inr q => exact ((ordinaryOldRim_old_private G a q).mp h.1).elim
  · exact ((ordinaryOldRim_private_any G p b).mp h.1).elim

theorem ordinaryAttachment_spoke_disjoint (H : V → U → Prop) (z : W) (ρ : I → V) :
    ∀ a b,¬(ordinaryOldSpokes H a b ∧ ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ a b) := by
  intro a b
  cases a <;> cases b <;> simp [ordinaryOldSpokes,ordinaryAttachmentSpokes]

theorem ordinaryAttachment_resources_union (G : SimpleGraph V) (H : V → U → Prop)
    (C : SimpleGraph W) (z : W) (ρ : I → V) :
    ordinaryHostResources (ordinaryAttachmentRim G C z ρ) (ordinaryAttachmentSpokes H z ρ)=
      ordinaryHostResources (ordinaryOldRim G) (ordinaryOldSpokes H)∪
      ordinaryHostResources (ordinaryAttachmentRim ⊥ C z ρ)
        (ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ) := by
  rw [ordinaryAttachment_rim_union,ordinaryAttachment_spoke_union,ordinaryHostResources_union]

theorem ordinaryAttachment_resources_disjoint (G : SimpleGraph V) (H : V → U → Prop)
    (C : SimpleGraph W) (z : W) (ρ : I → V) :
    Disjoint (ordinaryHostResources (ordinaryOldRim G) (ordinaryOldSpokes H))
      (ordinaryHostResources (ordinaryAttachmentRim ⊥ C z ρ)
        (ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ)) :=
  ordinaryHostResources_disjoint _ _ _ _ (ordinaryAttachment_rim_disjoint G C z ρ)
    (ordinaryAttachment_spoke_disjoint H z ρ)

theorem ordinaryAttachment_extra_resources (G : SimpleGraph V) (H : V → U → Prop)
    (C : SimpleGraph W) (z : W) (ρ : I → V) :
    ordinaryHostResources (ordinaryAttachmentRim G C z ρ) (ordinaryAttachmentSpokes H z ρ)\
      ordinaryHostResources (ordinaryOldRim G) (ordinaryOldSpokes H)=
    ordinaryHostResources (ordinaryAttachmentRim ⊥ C z ρ)
      (ordinaryAttachmentSpokes (fun (_ : V) (_ : U) => False) z ρ) := by
  rw [ordinaryAttachment_resources_union]
  have hd := ordinaryAttachment_resources_disjoint G H C z ρ
  ext e
  simp only [Finset.mem_sdiff,Finset.mem_union]
  constructor
  · rintro ⟨he,hnot⟩;exact he.resolve_left hnot
  · intro he
    exact ⟨Or.inr he,fun ho => Finset.disjoint_left.mp hd ho he⟩

theorem ordinaryAttachment_divisible (G : SimpleGraph V) (H : V → U → Prop)
    (C : SimpleGraph W) (hC : IsEmbeddedCycle C r) (z : W) (ρ : I → V)
    (hfull : ∀ w,w∈C.support)
    (hG : ∀ a,G.degree a=2*(Finset.univ.filter (H a)).card)
    (hH : ∀ b,r ∣ (Finset.univ.filter (fun a => H a b)).card) :
    (∀ a,(ordinaryAttachmentRim G C z ρ).degree a=2*(Finset.univ.filter (ordinaryAttachmentSpokes H z ρ a)).card) ∧
    (∀ b,r ∣ (Finset.univ.filter (fun a => ordinaryAttachmentSpokes H z ρ a b)).card) := by
  have hnew := ordinary_wheel_decomposition_balance _ _ r
    (ordinaryAttachment_extra_wheel_decomposition (U:=U) C hC z ρ hfull)
  have hb := ordinary_balance_disjoint_union _ _ _ _ (ordinaryAttachment_rim_disjoint G C z ρ)
    (ordinaryAttachment_spoke_disjoint H z ρ) (ordinaryOldPair_balance (X:=I×W) (I:=I) G H hG) hnew.1
  have hd := ordinary_hub_divisibility_disjoint_union _ _ r (ordinaryAttachment_spoke_disjoint H z ρ)
    (ordinaryOldPair_hub_divisibility (X:=I×W) (I:=I) H r hH) hnew.2
  simp only [←SimpleGraph.ncard_neighborSet] at hb ⊢
  rw [←ordinaryAttachment_rim_union] at hb
  rw [ordinaryAttachment_spoke_union]
  simp only [card_filter_naturalIndicator] at hb hd ⊢
  exact ⟨hb,hd⟩

end Oberwolfach
