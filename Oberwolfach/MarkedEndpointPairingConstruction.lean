module

public import Oberwolfach.MarkedEndpointPairingWitness
public import Oberwolfach.PhysicalSpokeDeletion
public import Oberwolfach.BipartiteBlockAfterDeletion

@[expose] public section

/-! Construct endpoint assignments avoiding any physical graph within the
explicit degree budget. The five Hall blocks are checked after the actual
spoke deletion; their existence is not an assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

namespace MarkedEndpointPairing
variable {A₀ A₁ X₀ X₁ : Finset V} {Y₀ Y₁ : Finset U}
    {H₀ HK : V→U→Prop} {π : Equiv.Perm V} {b : ℕ}

def mono (P : MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b)
    (H₀' HK' : V→U→Prop) (h₀ : ∀ v u,H₀ v u→H₀' v u) (hK : ∀ v u,HK v u→HK' v u) :
    MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀' HK' π b where
  hubs_disjoint:=P.hubs_disjoint
  incoming:=P.incoming
  outgoing:=P.outgoing
  incoming_adj:=fun a=>⟨(P.incoming_adj a).1,h₀ _ _ (P.incoming_adj a).2⟩
  outgoing_adj:=by
    intro x
    refine ⟨(P.outgoing_adj x).1,?_⟩
    have hh:=(P.outgoing_adj x).2
    split_ifs at hh ⊢ with h
    · exact hK _ _ hh
    · exact h₀ _ _ hh
  separated:=P.separated

theorem mono_graph (P : MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b)
    (H₀' HK' : V→U→Prop) (h₀ : ∀ v u,H₀ v u→H₀' v u) (hK : ∀ v u,HK v u→HK' v u) :
    (P.mono H₀' HK' h₀ hK).graph=P.graph := rfl

end MarkedEndpointPairing

theorem marked_endpoint_pairing_from_blocks
    (A₀ A₁ X₀ X₁ : Finset V) (Y₀ Y₁ : Finset U) (hY : Disjoint Y₀ Y₁)
    (H₀ HK : V→U→Prop) (π : Equiv.Perm V) (b : ℕ)
    (hbalA : A₀.card+A₁.card=Y₀.card+Y₁.card)
    (hbalX : X₀.card+X₁.card=Y₀.card+Y₁.card) (hmarked : A₁.card=Y₁.card)
    (degree tau lam : ℝ) (htau : 0<tau) (hlam : 0<lam)
    (hdeg : 2*tau+(2*(2*b+1):ℕ)≤degree) (hmargin : (2*(2*b+1):ℕ)<lam*tau)
    (hgap : (X₁.card:ℝ)+2*tau≤Y₀.card)
    (B₁ : BipartiteBlockBounds H₀ (fun a=>a∈A₁) (fun y=>y∈Y₁) degree tau lam)
    (B₂ : BipartiteBlockBounds H₀ (fun a=>a∈A₀) (fun y=>y∈Y₀) degree tau lam)
    (B₃ : BipartiteBlockBounds HK (fun a=>a∈X₁) (fun y=>y∈Y₀) degree tau lam)
    (B₄ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₀) degree tau lam)
    (B₅ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₁) degree tau lam) :
    Nonempty (MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b) := by
  obtain ⟨D₁,D₂,D₃,D₄,D₅⟩:=marked_endpoint_assignment_blocks A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK
    degree tau lam B₁ B₂ B₃ B₄ B₅
  obtain ⟨f,g,hf,hg,_hftype,_hgtype,hapart⟩:=marked_typed_endpoint_pairing_of_bounds (A:=A₀⊕A₁) (X:=X₀⊕X₁) (Y:=Y₀⊕Y₁)
    (markedIncomingAssignment A₀ A₁ Y₀ Y₁ H₀) (markedOutgoingAssignment X₀ X₁ Y₀ Y₁ H₀ HK)
    (fun a=>a.isRight=true) (fun x=>x.isRight=true) (fun y=>y.isRight=true)
    (by simpa using hbalA) (by simpa using hbalX)
    (by simp only [Fintype.card_subtype,tagged_right_card,hmarked])
    (by intro x y h hx;exact fun hy=>h.1 ⟨hx,hy⟩)
    π b 2 (taggedSubsetValue A₀ A₁) (taggedSubsetValue X₀ X₁)
    (by convert tagged_subset_label_fibre A₀ A₁ using 1 <;> congr!)
    (by convert tagged_subset_label_fibre X₀ X₁ using 1 <;> congr!)
    degree tau lam htau hlam hdeg hmargin
    (by
      have hX' := tagged_right_card X₀ X₁
      have hY' := tagged_left_card Y₀ Y₁
      have hh := hgap
      rw [←hX',←hY'] at hh
      convert hh using 1 <;> congr!) D₁ D₂ D₃ D₄ D₅
  exact ⟨⟨hY,f,g,hf,hg,hapart⟩⟩

theorem marked_endpoint_pairing_after_physical_deletion
    (A₀ A₁ X₀ X₁ : Finset V) (Y₀ Y₁ : Finset U) (hY : Disjoint Y₀ Y₁)
    (H₀ HK : V→U→Prop) (π : Equiv.Perm V) (b : ℕ)
    (hbalA : A₀.card+A₁.card=Y₀.card+Y₁.card)
    (hbalX : X₀.card+X₁.card=Y₀.card+Y₁.card) (hmarked : A₁.card=Y₁.card)
    (degree tau lam loss : ℝ) (htau : 0<tau) (hlam : 0<lam)
    (hdeg : 2*tau+(2*(2*b+1):ℕ)≤degree) (hmargin : (2*(2*b+1):ℕ)<lam*tau)
    (hgap : (X₁.card:ℝ)+2*tau≤Y₀.card) (hcutloss : loss≤lam*tau)
    (B₁ : BipartiteBlockBounds H₀ (fun a=>a∈A₁) (fun y=>y∈Y₁) (degree+loss) tau (2*lam))
    (B₂ : BipartiteBlockBounds H₀ (fun a=>a∈A₀) (fun y=>y∈Y₀) (degree+loss) tau (2*lam))
    (B₃ : BipartiteBlockBounds HK (fun a=>a∈X₁) (fun y=>y∈Y₀) (degree+loss) tau (2*lam))
    (B₄ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₀) (degree+loss) tau (2*lam))
    (B₅ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₁) (degree+loss) tau (2*lam))
    (D : SimpleGraph (V⊕U)) (hD : ∀ z,(D.degree z:ℝ)≤loss) :
    ∃ P:MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK π b,Disjoint P.graph D := by
  let J v u:=D.Adj (Sum.inl v) (Sum.inr u)
  have hrow (v:V):((Finset.univ.filter (J v)).card:ℝ)≤loss:=
    (Nat.cast_le.mpr (physical_spoke_deleted_row D v)).trans (hD (Sum.inl v))
  have hcol (u:U):((Finset.univ.filter (fun v=>J v u)).card:ℝ)≤loss:=
    (Nat.cast_le.mpr (physical_spoke_deleted_col D u)).trans (hD (Sum.inr u))
  have hblock (H:V→U→Prop) (A:Finset V) (B:Finset U)
      (h:BipartiteBlockBounds H (fun a=>a∈A) (fun y=>y∈B) (degree+loss) tau (2*lam)):
      BipartiteBlockBounds (fun v u=>H v u∧¬J v u) (fun a=>a∈A) (fun y=>y∈B) degree tau lam:=
    bipartite_block_after_deletion H J _ _ degree tau lam loss hlam.le h hrow hcol hcutloss
  obtain ⟨P⟩:=marked_endpoint_pairing_from_blocks A₀ A₁ X₀ X₁ Y₀ Y₁ hY
    (fun v u=>H₀ v u∧¬J v u) (fun v u=>HK v u∧¬J v u) π b hbalA hbalX hmarked
    degree tau lam htau hlam hdeg hmargin hgap
    (hblock _ _ _ B₁) (hblock _ _ _ B₂) (hblock _ _ _ B₃) (hblock _ _ _ B₄) (hblock _ _ _ B₅)
  refine ⟨P.mono H₀ HK (fun _ _ h=>h.1) (fun _ _ h=>h.1),?_⟩
  rw [MarkedEndpointPairing.mono_graph]
  apply disjoint_iff_inf_le.mpr
  intro z w hzw
  have hh:=P.graph_le hzw.1
  cases z <;> cases w
  · exact False.elim hh
  · exact (hh.elim (fun h=>h.2) (fun h=>h.2)) hzw.2
  · exact (hh.elim (fun h=>h.2) (fun h=>h.2)) hzw.2.symm
  · exact False.elim hh

end Oberwolfach
