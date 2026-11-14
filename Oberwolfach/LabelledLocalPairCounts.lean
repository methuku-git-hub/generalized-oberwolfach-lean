module

public import Oberwolfach.RootedLocalPrescriptions

@[expose] public section

/-! Two prescribed distinct free vertices cost two free positions in
an absorber count. This is the local bound used for forbidden edges
whose displayed endpoints are both outside the root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype T] [DecidableEq T] {c : ℕ}

theorem labelled_absorber_local_free_pair_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (x y : V) (hxy : x≠y) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
      x∈labelledAbsorberFree R (S D.1) X D.2 ∧ y∈labelledAbsorberFree R (S D.1) X D.2} ≤
      (c*c)^2*Fintype.card T*X.card^c*Y.card^(c*c-2)*J^(2*c+1) := by
  let F := LabelledAbsorberFamily R S X
  let Q (p : Fin (c*c) × Fin (c*c)) (D : F) :=
    (∀ i : Fin (c*c),D.2.1.val (Sum.inl i)∈Y) ∧
      D.2.1.val (Sum.inl p.1)=x ∧ D.2.1.val (Sum.inl p.2)=y
  have hc (p : Fin (c*c) × Fin (c*c)) : Fintype.card {D : F // Q p D} ≤
      Fintype.card T*(X.card^c*Y.card^(c*c-2)*J^(2*c+1)) := by
    by_cases hp : p.1=p.2
    · have hn (D : F) : ¬Q p D := by
        rintro ⟨_,hx,hy⟩
        exact hxy (hx.symm.trans (hp ▸ hy))
      simp only [Fintype.card_subtype,hn,Finset.filter_false,Finset.card_empty,Nat.zero_le]
    · have he : Fintype.card {D : F // Q p D}=
          ∑ t,Fintype.card {D : LabelledCycleRecord R (S t).val X //
            (∀ i : Fin (c*c),D.1.val (Sum.inl i)∈Y) ∧
              D.1.val (Sum.inl p.1)=x ∧ D.1.val (Sum.inl p.2)=y} := by
        convert finite_sigma_predicate_card (fun t (D : LabelledCycleRecord R (S t).val X) =>
          (∀ i : Fin (c*c),D.1.val (Sum.inl i)∈Y) ∧
            D.1.val (Sum.inl p.1)=x ∧ D.1.val (Sum.inl p.2)=y) using 1 <;> congr!
      rw [he]
      calc
        _ ≤ ∑ _t : T,X.card^c*Y.card^(c*c-2)*J^(2*c+1) := by
          apply Finset.sum_le_sum
          intro t _
          have hh := labelled_cycle_records_local_two_coordinate_count R (S t).val X Y J hJ p.1 p.2 hp x y
          simpa only [Fintype.card_sum,Fintype.card_fin,show c+(c+1)=2*c+1 by omega] using hh
        _ = _ := by simp
  have hp (D : F) :
      (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
        x∈labelledAbsorberFree R (S D.1) X D.2 ∧ y∈labelledAbsorberFree R (S D.1) X D.2) ↔ ∃ p,Q p D := by
    simp only [labelledAbsorberFree,Finset.image_subset_iff,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨h,⟨j,hj⟩,⟨k,hk⟩⟩
      exact ⟨⟨j,k⟩,fun i => h i trivial,hj,hk⟩
    · rintro ⟨⟨j,k⟩,h,hj,hk⟩
      exact ⟨fun i _ => h i,⟨j,hj⟩,⟨k,hk⟩⟩
  let A := Finset.univ.filter (fun D : F => labelledAbsorberFree R (S D.1) X D.2⊆Y ∧
    x∈labelledAbsorberFree R (S D.1) X D.2 ∧ y∈labelledAbsorberFree R (S D.1) X D.2)
  let B := fun p : Fin (c*c) × Fin (c*c) => Finset.univ.filter (Q p)
  have hsub : A⊆Finset.univ.biUnion B := by
    intro D hD
    obtain ⟨p,hpD⟩ := (hp D).mp (Finset.mem_filter.mp hD).2
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_univ _,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpD⟩⟩
  simp only [Fintype.card_subtype]
  change A.card ≤ _
  calc
    _ ≤ (Finset.univ.biUnion B).card := Finset.card_le_card hsub
    _ ≤ ∑ p : Fin (c*c) × Fin (c*c),(B p).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin (c*c) × Fin (c*c),Fintype.card T*(X.card^c*Y.card^(c*c-2)*J^(2*c+1)) := by
      apply Finset.sum_le_sum
      intro p _
      simpa only [Fintype.card_subtype,B] using hc p
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,smul_eq_mul]
      ring

end Oberwolfach
