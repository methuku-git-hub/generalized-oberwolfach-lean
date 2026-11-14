module

public import Oberwolfach.AbsorberFamilyCounts
public import Oberwolfach.FiniteFibreCounts
public import Oberwolfach.FiniteExistentialCounts

@[expose] public section

/-! Deleting vertices removes only the labelled absorbers whose free
maps meet those vertices. Root maps and all cycle identifiers stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C O T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype O] [DecidableEq O] [Fintype T] [DecidableEq T] {h c : ℕ}

theorem labelled_cycle_records_constrained_count (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X Y : Finset V)
    (P : Finset (Fin h ⊕ Fin c)) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) :
    Fintype.card {D : LabelledCycleRecord R S X // ∀ j∈P,D.1.val j∈Y} ≤
      X.card^c*Y.card^(freeLabelPositions P).card*
        Fintype.card V^(h-(freeLabelPositions P).card)*J^Fintype.card O := by
  let A := {D : LabelledCycleRecord R S X // ∀ j∈P,D.1.val j∈Y}
  let F := {f : RootedLabelMap V h c X // ∀ j∈P,f.val j∈Y}
  let B := Σ f : F,CycleIdentifierAssignments R S f.val.val
  let enc (D : A) : B := ⟨⟨D.val.1,D.property⟩,D.val.2⟩
  have hinj : Function.Injective enc := by
    intro D E he
    apply Subtype.ext
    exact congrArg (fun b : B => (⟨b.1.val,b.2⟩ : LabelledCycleRecord R S X)) he
  have hB : Fintype.card B ≤ Fintype.card F*J^Fintype.card O := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _f : F,J^Fintype.card O :=
        Finset.sum_le_sum (fun f _ => cycle_identifier_assignments_card R S J hJ f.val.val)
      _ = _ := by simp
  exact (Fintype.card_le_of_injective enc hinj).trans (hB.trans
    (Nat.mul_le_mul_right _ (rooted_label_maps_constrained_count X Y P)))

theorem labelled_cycle_record_free_coordinate_count (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) (j : Fin h) (v : V) :
    Fintype.card {D : LabelledCycleRecord R S X // D.1.val (Sum.inl j)=v} ≤
      X.card^c*Fintype.card V^(h-1)*J^Fintype.card O := by
  have hh := labelled_cycle_records_constrained_count R S X {v} {Sum.inl j} J hJ
  have he : freeLabelPositions ({Sum.inl j} : Finset (Fin h ⊕ Fin c))={j} := by
    ext k;simp [freeLabelPositions]
  simp only [he,Finset.card_singleton,pow_one,one_pow,mul_one] at hh
  have hp (D : LabelledCycleRecord R S X) :
      (∀ k∈({Sum.inl j} : Finset (Fin h ⊕ Fin c)),D.1.val k∈({v} : Finset V)) ↔
        D.1.val (Sum.inl j)=v := by simp
  have hcard := Fintype.card_congr (Equiv.subtypeEquivRight hp)
  calc
    _ = Fintype.card {D : LabelledCycleRecord R S X //
        ∀ k∈({Sum.inl j} : Finset (Fin h ⊕ Fin c)),D.1.val k∈({v} : Finset V)} := hcard.symm
    _ ≤ _ := hh

theorem labelled_absorber_free_vertex_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) (v : V) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      v∈labelledAbsorberFree R (S D.1) X D.2} ≤
      (c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1) := by
  have hc (j : Fin (c*c)) : Fintype.card {D : LabelledAbsorberFamily R S X //
      D.2.1.val (Sum.inl j)=v} ≤
      Fintype.card T*(X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1)) := by
    have he : Fintype.card {D : LabelledAbsorberFamily R S X // D.2.1.val (Sum.inl j)=v}=
        ∑ t,Fintype.card {D : LabelledCycleRecord R (S t).val X // D.1.val (Sum.inl j)=v} := by
      convert finite_sigma_predicate_card (fun t (D : LabelledCycleRecord R (S t).val X) =>
        D.1.val (Sum.inl j)=v) using 1 <;> congr!
    rw [he]
    calc
      _ ≤ ∑ _t : T,X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1) := by
        apply Finset.sum_le_sum
        intro t _
        have hh := labelled_cycle_record_free_coordinate_count R (S t).val X J hJ j v
        simpa only [Fintype.card_sum,Fintype.card_fin,show c+(c+1)=2*c+1 by omega] using hh
      _ = _ := by simp
  have hp (D : LabelledAbsorberFamily R S X) :
      v∈labelledAbsorberFree R (S D.1) X D.2 ↔ ∃ j : Fin (c*c),D.2.1.val (Sum.inl j)=v := by
    simp [labelledAbsorberFree]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hp)]
  calc
    _ ≤ ∑ j : Fin (c*c),Fintype.card {D : LabelledAbsorberFamily R S X // D.2.1.val (Sum.inl j)=v} := by
      convert finite_exists_card_le_sum (fun j (D : LabelledAbsorberFamily R S X) => D.2.1.val (Sum.inl j)=v) using 1 <;> congr!
    _ ≤ ∑ _j : Fin (c*c),Fintype.card T*(X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1)) :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul];ring

theorem labelled_absorber_free_deletion_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Z : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      ¬Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z} ≤
      Z.card*((c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1)) := by
  have hp (D : LabelledAbsorberFamily R S X) :
      ¬Disjoint (labelledAbsorberFree R (S D.1) X D.2) Z ↔
        ∃ v : Z,v.val∈labelledAbsorberFree R (S D.1) X D.2 := by
    constructor
    · intro hd
      by_contra hn
      exact hd (Finset.disjoint_right.mpr (fun v hv hw => hn ⟨⟨v,hv⟩,hw⟩))
    · rintro ⟨v,hv⟩ hd;exact Finset.disjoint_left.mp hd hv v.property
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hp)]
  calc
    _ ≤ ∑ v : Z,Fintype.card {D : LabelledAbsorberFamily R S X //
        v.val∈labelledAbsorberFree R (S D.1) X D.2} := by
      convert finite_exists_card_le_sum (fun (v : Z) (D : LabelledAbsorberFamily R S X) =>
        v.val∈labelledAbsorberFree R (S D.1) X D.2) using 1 <;> congr!
    _ ≤ ∑ _v : Z,(c*c)*Fintype.card T*X.card^c*Fintype.card V^(c*c-1)*J^(2*c+1) :=
      Finset.sum_le_sum (fun v _ => labelled_absorber_free_vertex_count R S X J hJ v.val)
    _ = _ := by simp

end Oberwolfach
