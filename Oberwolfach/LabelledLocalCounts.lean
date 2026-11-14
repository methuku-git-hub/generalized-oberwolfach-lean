module

public import Oberwolfach.LabelledRecordDeletionCounts

@[expose] public section

/-! Incidence counts for labelled absorbers whose free labels lie in a
specified set. The order in the bound is the size of this set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C O T : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
    [Fintype O] [DecidableEq O] [Fintype T] [DecidableEq T] {h c : ℕ}

theorem rooted_label_maps_local_coordinate_count (X Y : Finset V) (j : Fin h) (v : V) :
    Fintype.card {f : RootedLabelMap V h c X //
      (∀ k : Fin h,f.val (Sum.inl k)∈Y) ∧ f.val (Sum.inl j)=v} ≤
      X.card^c*Y.card^(h-1) := by
  let A := {f : RootedLabelMap V h c X //
      (∀ k : Fin h,f.val (Sum.inl k)∈Y) ∧ f.val (Sum.inl j)=v}
  let enc (f : A) : (Fin c → X) × ({k : Fin h // k≠j} → Y) :=
    (fun i => ⟨f.val.val (Sum.inr i),rootedLabelMap_root_mem X f.val i⟩,
     fun k => ⟨f.val.val (Sum.inl k.val),f.property.1 k.val⟩)
  have hi : Function.Injective enc := by
    intro f g he
    apply Subtype.ext
    apply Subtype.ext
    funext k
    rcases k with k | k
    · by_cases hk : k=j
      · subst k;exact f.property.2.trans g.property.2.symm
      · exact congrArg (fun y : Y => y.val) (congrFun (congrArg Prod.snd he) ⟨k,hk⟩)
    · exact congrArg (fun x : X => x.val) (congrFun (congrArg Prod.fst he) k)
  have hn : Fintype.card {k : Fin h // k≠j}=h-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,hn] using
    Fintype.card_le_of_injective enc hi

theorem labelled_cycle_records_local_coordinate_count (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) (j : Fin h) (v : V) :
    Fintype.card {D : LabelledCycleRecord R S X //
      (∀ k : Fin h,D.1.val (Sum.inl k)∈Y) ∧ D.1.val (Sum.inl j)=v} ≤
      X.card^c*Y.card^(h-1)*J^Fintype.card O := by
  let A := {D : LabelledCycleRecord R S X //
      (∀ k : Fin h,D.1.val (Sum.inl k)∈Y) ∧ D.1.val (Sum.inl j)=v}
  let F := {f : RootedLabelMap V h c X //
      (∀ k : Fin h,f.val (Sum.inl k)∈Y) ∧ f.val (Sum.inl j)=v}
  let B := Σ f : F,CycleIdentifierAssignments R S f.val.val
  let enc (D : A) : B := ⟨⟨D.val.1,D.property⟩,D.val.2⟩
  have hi : Function.Injective enc := by
    intro D E he
    apply Subtype.ext
    exact congrArg (fun b : B => (⟨b.1.val,b.2⟩ : LabelledCycleRecord R S X)) he
  have hb : Fintype.card B ≤ Fintype.card F*J^Fintype.card O := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _f : F,J^Fintype.card O := Finset.sum_le_sum
        (fun f _ => cycle_identifier_assignments_card R S J hJ f.val.val)
      _ = _ := by simp
  exact (Fintype.card_le_of_injective enc hi).trans (hb.trans
    (Nat.mul_le_mul_right _ (rooted_label_maps_local_coordinate_count X Y j v)))

theorem labelled_absorber_local_free_vertex_count (R : C → Finset V)
    (S : T → VertexAbsorberTemplate c) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J) (v : V) :
    Fintype.card {D : LabelledAbsorberFamily R S X //
      labelledAbsorberFree R (S D.1) X D.2⊆Y ∧ v∈labelledAbsorberFree R (S D.1) X D.2} ≤
      (c*c)*Fintype.card T*X.card^c*Y.card^(c*c-1)*J^(2*c+1) := by
  have hc (j : Fin (c*c)) : Fintype.card {D : LabelledAbsorberFamily R S X //
      (∀ k : Fin (c*c),D.2.1.val (Sum.inl k)∈Y) ∧ D.2.1.val (Sum.inl j)=v} ≤
      Fintype.card T*(X.card^c*Y.card^(c*c-1)*J^(2*c+1)) := by
    have he : Fintype.card {D : LabelledAbsorberFamily R S X //
        (∀ k : Fin (c*c),D.2.1.val (Sum.inl k)∈Y) ∧ D.2.1.val (Sum.inl j)=v}=
        ∑ t,Fintype.card {D : LabelledCycleRecord R (S t).val X //
        (∀ k : Fin (c*c),D.1.val (Sum.inl k)∈Y) ∧ D.1.val (Sum.inl j)=v} := by
      convert finite_sigma_predicate_card (fun t (D : LabelledCycleRecord R (S t).val X) =>
        (∀ k : Fin (c*c),D.1.val (Sum.inl k)∈Y) ∧ D.1.val (Sum.inl j)=v) using 1 <;> congr!
    rw [he]
    calc
      _ ≤ ∑ _t : T,X.card^c*Y.card^(c*c-1)*J^(2*c+1) := by
        apply Finset.sum_le_sum
        intro t _
        have hh := labelled_cycle_records_local_coordinate_count R (S t).val X Y J hJ j v
        simpa only [Fintype.card_sum,Fintype.card_fin,show c+(c+1)=2*c+1 by omega] using hh
      _ = _ := by simp
  have hp (D : LabelledAbsorberFamily R S X) :
      (labelledAbsorberFree R (S D.1) X D.2⊆Y ∧ v∈labelledAbsorberFree R (S D.1) X D.2) ↔
      ∃ j : Fin (c*c),(∀ k : Fin (c*c),D.2.1.val (Sum.inl k)∈Y) ∧ D.2.1.val (Sum.inl j)=v := by
    simp only [labelledAbsorberFree,Finset.image_subset_iff,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨h,⟨j,hj⟩⟩;exact ⟨j,fun k => h k trivial,hj⟩
    · rintro ⟨j,h,hj⟩;exact ⟨fun k _ => h k,⟨j,hj⟩⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hp)]
  calc
    _ ≤ ∑ j : Fin (c*c),Fintype.card {D : LabelledAbsorberFamily R S X //
        (∀ k : Fin (c*c),D.2.1.val (Sum.inl k)∈Y) ∧ D.2.1.val (Sum.inl j)=v} := by
      convert finite_exists_card_le_sum (fun j (D : LabelledAbsorberFamily R S X) =>
        (∀ k : Fin (c*c),D.2.1.val (Sum.inl k)∈Y) ∧ D.2.1.val (Sum.inl j)=v) using 1 <;> congr!
    _ ≤ ∑ _j : Fin (c*c),Fintype.card T*(X.card^c*Y.card^(c*c-1)*J^(2*c+1)) :=
      Finset.sum_le_sum (fun j _ => hc j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul];ring

end Oberwolfach
