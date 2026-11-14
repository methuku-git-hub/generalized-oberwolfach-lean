module

public import Oberwolfach.RootedLabelMaps
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

/-! Counts retain every cycle identifier in a labelled realization.
Different identifiers on the same vertex set are bounded by J, and are
not identified by the encoding. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C O : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] [Fintype O] [DecidableEq O]
    {h c : ℕ}

abbrev CycleIdentifierAssignments (R : C → Finset V) (S : O → Finset (Fin h ⊕ Fin c))
    (f : Fin h ⊕ Fin c → V) := ∀ o,{C₀ : C // R C₀=(S o).image f}

abbrev LabelledCycleRecord (R : C → Finset V) (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V) :=
  Σ f : RootedLabelMap V h c X,CycleIdentifierAssignments R S f.val

theorem cycle_identifier_assignments_card (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) (f : Fin h ⊕ Fin c → V) :
    Fintype.card (CycleIdentifierAssignments R S f) ≤ J^Fintype.card O := by
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _o : O,J := Finset.prod_le_prod' (fun o _ => hJ ((S o).image f))
    _ = _ := by simp

theorem labelled_cycle_records_card (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) :
    Fintype.card (LabelledCycleRecord R S X) ≤
      X.card^c*Fintype.card V^h*J^Fintype.card O := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _f : RootedLabelMap V h c X,J^Fintype.card O :=
      Finset.sum_le_sum (fun f _ => cycle_identifier_assignments_card R S J hJ f.val)
    _ = Fintype.card (RootedLabelMap V h c X)*J^Fintype.card O := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (rooted_label_maps_count X)

theorem labelled_cycle_records_occurrence_card (R : C → Finset V)
    (S : O → Finset (Fin h ⊕ Fin c)) (X : Finset V) (J : ℕ)
    (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J) (o : O) (C₀ : C) :
    Fintype.card {D : LabelledCycleRecord R S X // (D.2 o).val=C₀} ≤
      X.card^c*(R C₀).card^(freeLabelPositions (S o)).card*
        Fintype.card V^(h-(freeLabelPositions (S o)).card)*J^Fintype.card O := by
  let A := {D : LabelledCycleRecord R S X // (D.2 o).val=C₀}
  let F := {f : RootedLabelMap V h c X // ∀ j∈S o,f.val j∈R C₀}
  let B := Σ f : F,CycleIdentifierAssignments R S f.val.val
  let enc (D : A) : B := ⟨⟨D.val.1,by
    intro j hj
    have he : R C₀=(S o).image D.val.1.val := by
      simpa only [D.property] using (D.val.2 o).property
    rw [he]
    exact Finset.mem_image.mpr ⟨j,hj,rfl⟩⟩,D.val.2⟩
  have hinj : Function.Injective enc := by
    intro D E he
    apply Subtype.ext
    have hh := congrArg (fun b : B => (⟨b.1.val,b.2⟩ : LabelledCycleRecord R S X)) he
    exact hh
  have hB : Fintype.card B ≤ Fintype.card F*J^Fintype.card O := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _f : F,J^Fintype.card O :=
        Finset.sum_le_sum (fun f _ => cycle_identifier_assignments_card R S J hJ f.val.val)
      _ = _ := by simp
  exact (Fintype.card_le_of_injective enc hinj).trans (hB.trans
    (Nat.mul_le_mul_right _ (rooted_label_maps_constrained_count X (R C₀) (S o))))

end Oberwolfach
