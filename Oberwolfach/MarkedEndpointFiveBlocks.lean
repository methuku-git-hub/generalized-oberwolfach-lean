module

public import Oberwolfach.MarkedEndpointPairingConstruction

@[expose] public section

/-! The five blocks in the marked endpoint argument, in order:
A₁--Y₁ via H₀, A₀--Y₀ via H₀, X₁--Y₀ via HK,
X₀--Y₀ via H₀, X₀--Y₁ via H₀. A is incoming and X outgoing.
The functions record the actual direction, rim type and spoke types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedEndpointFiveRimType:Fin 5→Bool:=![true,false,true,false,false]
def markedEndpointFiveIncoming:Fin 5→Bool:=![true,true,false,false,false]
def markedEndpointFiveRootSpokeType:Fin 5→Bool:=![true,false,false,false,true]
def markedEndpointFiveLabelSpokeType:Fin 5→Bool:=![false,false,true,false,false]
def markedEndpointFiveRows {V:Type} (A₀ A₁ X₀ X₁:Finset V):Fin 5→Finset V:=![A₁,A₀,X₁,X₀,X₀]
def markedEndpointFiveHubs {U:Type} (Y₀ Y₁:Finset U):Fin 5→Finset U:=![Y₁,Y₀,Y₀,Y₀,Y₁]

theorem marked_endpoint_pairing_from_five_deleted_blocks
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (H:Bool→V→U→Prop) (π:Equiv.Perm V) (b:ℕ)
    (A₀ A₁ X₀ X₁:Finset V) (Y₀ Y₁:Finset U)
    (hY:Disjoint Y₀ Y₁)
    (hbalA:A₀.card+A₁.card=Y₀.card+Y₁.card)
    (hbalX:X₀.card+X₁.card=Y₀.card+Y₁.card) (hmarked:A₁.card=Y₁.card)
    (degree tau lam:ℝ) (htau:0<tau) (hlam:0<lam)
    (hdeg:2*tau+(2*(2*b+1):ℕ)≤degree) (hmargin:(2*(2*b+1):ℕ)<lam*tau)
    (hgap:(X₁.card:ℝ)+2*tau≤Y₀.card) (D:SimpleGraph (V⊕U))
    (hblocks:∀ j:Fin 5,BipartiteBlockBounds
      (fun v u=>H (markedEndpointFiveLabelSpokeType j) v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
      (fun v=>v∈markedEndpointFiveRows A₀ A₁ X₀ X₁ j)
      (fun u=>u∈markedEndpointFiveHubs Y₀ Y₁ j) degree tau lam):
    ∃ P:MarkedEndpointPairing A₀ A₁ X₀ X₁ Y₀ Y₁ (H false) (H true) π b,Disjoint P.graph D := by
  have h0:=hblocks 0
  have h1:=hblocks 1
  have h2:=hblocks 2
  have h3:=hblocks 3
  have h4:=hblocks 4
  simp only [markedEndpointFiveLabelSpokeType,markedEndpointFiveRows,markedEndpointFiveHubs,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ] at h0 h1 h2 h3 h4
  obtain ⟨P⟩:=marked_endpoint_pairing_from_blocks A₀ A₁ X₀ X₁ Y₀ Y₁ hY
    (fun v u=>H false v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
    (fun v u=>H true v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
    π b hbalA hbalX hmarked degree tau lam htau hlam hdeg hmargin hgap h0 h1 h2 h3 h4
  refine ⟨P.mono (H false) (H true) (fun _ _ h=>h.1) (fun _ _ h=>h.1),?_⟩
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
