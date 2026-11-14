module

public import Oberwolfach.AbsorberTemplateGeometry

@[expose] public section

/-! Occurrence bounds for one specified indexed cycle. A root-free cycle
fixes c free labels; a cycle meeting roots fixes at least c-1. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] {c : ℕ}

theorem labelled_absorber_occurrence_disjoint (hc : 1 ≤ c) (R : C → Finset V)
    (S : VertexAbsorberTemplate c) (X : Finset V) (hX : X.card=c) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (o : Fin c ⊕ Fin (c+1)) (C₀ : C) (hC : (R C₀).card=c) (hd : Disjoint (R C₀) X) :
    Fintype.card {D : LabelledCycleRecord R S.val X // (D.2 o).val=C₀} ≤
      c^(2*c)*Fintype.card V^(c*c-c)*J^(2*c+1) := by
  by_cases hz : rootLabelPositions (S.val o)=∅
  · have hfree : (freeLabelPositions (S.val o)).card=c := by
      have hh := label_positions_card (S.val o)
      simp only [hz,Finset.card_empty,S.property.1 o,add_zero] at hh
      exact hh
    have hh := labelled_cycle_records_occurrence_card R S.val X J hJ o C₀
    simp only [hX,hC,hfree,Fintype.card_sum,Fintype.card_fin,show c+(c+1)=2*c+1 by omega] at hh
    rw [show c^(2*c)=c^c*c^c by rw [show 2*c=c+c by omega,pow_add]]
    convert hh using 1 <;> congr!
  · let A := {D : LabelledCycleRecord R S.val X // (D.2 o).val=C₀}
    letI : IsEmpty A := ⟨fun D => hz (rooted_label_cycle_disjoint X (R C₀) (S.val o) D.val.1
      (by simpa only [D.property] using (D.val.2 o).property.symm) hd)⟩
    exact (show Fintype.card A=0 from Fintype.card_eq_zero).le.trans (Nat.zero_le _)

theorem labelled_absorber_occurrence_general (hc : 1 ≤ c) (R : C → Finset V)
    (S : VertexAbsorberTemplate c) (X : Finset V) (hX : X.card=c) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (o : Fin c ⊕ Fin (c+1)) (C₀ : C) (hC : (R C₀).card=c) :
    Fintype.card {D : LabelledCycleRecord R S.val X // (D.2 o).val=C₀} ≤
      c^(2*c)*Fintype.card V^(c*c-c+1)*J^(2*c+1) := by
  have hpart := label_positions_card (S.val o)
  rw [S.property.1 o] at hpart
  have hroot := S.property.2.2.2.2.2 o
  have hd : (freeLabelPositions (S.val o)).card ≤ c := by omega
  have hexp : c*c-(freeLabelPositions (S.val o)).card ≤ c*c-c+1 := by omega
  have hn : 0 < Fintype.card V := by
    have hh := Finset.card_le_univ X
    rw [hX] at hh
    omega
  have hh := labelled_cycle_records_occurrence_card R S.val X J hJ o C₀
  rw [hX,hC,Fintype.card_sum,Fintype.card_fin,Fintype.card_fin,show c+(c+1)=2*c+1 by omega] at hh
  apply hh.trans
  have hcp := Nat.pow_le_pow_right (show 0<c by omega) hd
  have hnp := Nat.pow_le_pow_right hn hexp
  have he : c^(2*c)=c^c*c^c := by rw [show 2*c=c+c by omega,pow_add]
  rw [he]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ hcp) hnp)

end Oberwolfach
