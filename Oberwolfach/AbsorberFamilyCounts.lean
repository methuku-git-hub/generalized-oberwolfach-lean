module

public import Oberwolfach.AbsorberOccurrenceCounts
public import Oberwolfach.LabelledAbsorberFactors

@[expose] public section

/-! Passing from individual template occurrences to any allowed finite
family of labelled absorbers, without forgetting their identifiers. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype T] {c : ℕ}

abbrev LabelledAbsorberFamily (R : C → Finset V) (S : T → VertexAbsorberTemplate c) (X : Finset V) :=
  Σ t,LabelledCycleRecord R (S t).val X

theorem labelled_absorber_family_occurrence_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) (C₀ : C) (B : ℕ)
    (hB : ∀ t o,Fintype.card {D : LabelledCycleRecord R (S t).val X // (D.2 o).val=C₀} ≤ B) :
    Fintype.card {D : LabelledAbsorberFamily R S X // ∃ o,(D.2.2 o).val=C₀} ≤
      (2*c+1)*Fintype.card T*B := by
  let F := LabelledAbsorberFamily R S X
  let P (o : Fin c ⊕ Fin (c+1)) := Finset.univ.filter (fun D : F => (D.2.2 o).val=C₀)
  have hp (o : Fin c ⊕ Fin (c+1)) : (P o).card ≤ Fintype.card T*B := by
    let e : {D : F // (D.2.2 o).val=C₀} ≃
        Σ t,{D : LabelledCycleRecord R (S t).val X // (D.2 o).val=C₀} := {
      toFun D := ⟨D.val.1,⟨D.val.2,D.property⟩⟩
      invFun D := ⟨⟨D.1,D.2.val⟩,D.2.property⟩
      left_inv := by rintro ⟨⟨t,D⟩,h⟩;rfl
      right_inv := by rintro ⟨t,⟨D,h⟩⟩;rfl }
    have he := Fintype.card_congr e
    calc
      _ = ∑ t,Fintype.card {D : LabelledCycleRecord R (S t).val X // (D.2 o).val=C₀} := by
        simpa only [Fintype.card_subtype,Fintype.card_sigma,P] using he
      _ ≤ ∑ _t : T,B := Finset.sum_le_sum (fun t _ => hB t o)
      _ = _ := by simp
  have he : Finset.univ.filter (fun D : F => ∃ o,(D.2.2 o).val=C₀)=Finset.univ.biUnion P := by
    ext D;simp [P]
  rw [Fintype.card_subtype,he]
  apply Finset.card_biUnion_le.trans
  calc
    _ ≤ ∑ _o : Fin c ⊕ Fin (c+1),Fintype.card T*B := Finset.sum_le_sum (fun o _ => hp o)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_sum,Fintype.card_fin,smul_eq_mul]
      ring

theorem labelled_absorber_subfamily_occurrence_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) (C₀ : C) (B : ℕ)
    (hB : ∀ t o,Fintype.card {D : LabelledCycleRecord R (S t).val X // (D.2 o).val=C₀} ≤ B)
    (A : Finset (LabelledAbsorberFamily R S X)) :
    Fintype.card {D : A // ∃ o,(D.val.2.2 o).val=C₀} ≤ (2*c+1)*Fintype.card T*B := by
  let enc (D : {D : A // ∃ o,(D.val.2.2 o).val=C₀}) :
      {D : LabelledAbsorberFamily R S X // ∃ o,(D.2.2 o).val=C₀} := ⟨D.val.val,D.property⟩
  have hinj : Function.Injective enc := by
    intro D E he;apply Subtype.ext;apply Subtype.ext
    exact congrArg (fun z : {D : LabelledAbsorberFamily R S X // ∃ o,(D.2.2 o).val=C₀} => z.val) he
  exact (Fintype.card_le_of_injective enc hinj).trans
    (labelled_absorber_family_occurrence_count R S X C₀ B hB)

end Oberwolfach
