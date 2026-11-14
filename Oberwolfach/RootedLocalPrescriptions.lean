module

public import Oberwolfach.LabelledLocalCounts

@[expose] public section

/-! Prescribing free labels inside a fixed local vertex set. Root
labels and indexed cycle choices are retained in the finite encoding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 3600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C O : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O] {h c : ℕ}

theorem rooted_label_maps_local_prescription_count (X Y : Finset V)
    (P : Finset (Fin h)) (g : Fin h → V) :
    Fintype.card {f : RootedLabelMap V h c X //
      (∀ j : Fin h,f.val (Sum.inl j)∈Y) ∧ (∀ j∈P,f.val (Sum.inl j)=g j)} ≤
      X.card^c*Y.card^(h-P.card) := by
  let A := {f : RootedLabelMap V h c X //
    (∀ j : Fin h,f.val (Sum.inl j)∈Y) ∧ (∀ j∈P,f.val (Sum.inl j)=g j)}
  let enc (f : A) : (Fin c → X) × ({j : Fin h // j∉P} → Y) :=
    (fun i => ⟨f.val.val (Sum.inr i),rootedLabelMap_root_mem X f.val i⟩,
     fun j => ⟨f.val.val (Sum.inl j.val),f.property.1 j.val⟩)
  have hi : Function.Injective enc := by
    intro f g' he
    apply Subtype.ext
    apply Subtype.ext
    funext j
    rcases j with j | j
    · by_cases hj : j∈P
      · exact (f.property.2 j hj).trans (g'.property.2 j hj).symm
      · exact congrArg (fun y : Y => y.val) (congrFun (congrArg Prod.snd he) ⟨j,hj⟩)
    · exact congrArg (fun x : X => x.val) (congrFun (congrArg Prod.fst he) j)
  have hn : Fintype.card {j : Fin h // j∉P}=h-P.card := by
    rw [Fintype.card_subtype_compl]
    simp
  simpa only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,hn] using
    Fintype.card_le_of_injective enc hi

theorem labelled_cycle_records_local_prescription_count (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (P : Finset (Fin h)) (g : Fin h → V) :
    Fintype.card {D : LabelledCycleRecord R S X //
      (∀ j : Fin h,D.1.val (Sum.inl j)∈Y) ∧ (∀ j∈P,D.1.val (Sum.inl j)=g j)} ≤
      X.card^c*Y.card^(h-P.card)*J^Fintype.card O := by
  let A := {D : LabelledCycleRecord R S X //
    (∀ j : Fin h,D.1.val (Sum.inl j)∈Y) ∧ (∀ j∈P,D.1.val (Sum.inl j)=g j)}
  let F := {f : RootedLabelMap V h c X //
    (∀ j : Fin h,f.val (Sum.inl j)∈Y) ∧ (∀ j∈P,f.val (Sum.inl j)=g j)}
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
    (Nat.mul_le_mul_right _ (rooted_label_maps_local_prescription_count X Y P g)))

theorem labelled_cycle_records_local_two_coordinate_count (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X Y : Finset V) (J : ℕ)
    (hJ : ∀ U : Finset V,Fintype.card {C₀ : C // R C₀=U} ≤ J)
    (j k : Fin h) (hjk : j≠k) (x y : V) :
    Fintype.card {D : LabelledCycleRecord R S X //
      (∀ i : Fin h,D.1.val (Sum.inl i)∈Y) ∧ D.1.val (Sum.inl j)=x ∧ D.1.val (Sum.inl k)=y} ≤
      X.card^c*Y.card^(h-2)*J^Fintype.card O := by
  have hh := labelled_cycle_records_local_prescription_count R S X Y J hJ {j,k} (fun i => if i=j then x else y)
  have hp (D : LabelledCycleRecord R S X) :
      ((∀ i : Fin h,D.1.val (Sum.inl i)∈Y) ∧
        (∀ i∈({j,k} : Finset (Fin h)),D.1.val (Sum.inl i)=(if i=j then x else y))) ↔
      ((∀ i : Fin h,D.1.val (Sum.inl i)∈Y) ∧ D.1.val (Sum.inl j)=x ∧ D.1.val (Sum.inl k)=y) := by
    simp [hjk,hjk.symm]
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hp)] at hh
  simpa only [Finset.card_pair hjk] using hh

end Oberwolfach
