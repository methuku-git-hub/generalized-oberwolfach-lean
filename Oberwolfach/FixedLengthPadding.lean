module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Pad graph-dependent selected lengths by zero on a fixed index set, so
all probabilistic thresholds may be chosen before the selection. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def padIndexedFunctions {I:Type} [Fintype I] [DecidableEq I] (S:Finset I) (X:I→Type)
    (w:∀ i:↥S,X i.val→ℝ) (i:I) (x:X i):ℝ:=
  if hi:i∈S then w ⟨i,hi⟩ x else 0

theorem pad_indexed_functions_on {I:Type} [Fintype I] [DecidableEq I] (S:Finset I) (X:I→Type)
    (w:∀ i:↥S,X i.val→ℝ) (i:↥S) (x:X i.val):
    padIndexedFunctions S X w i.val x=w i x:=by
  simp [padIndexedFunctions,i.property]

theorem pad_indexed_functions_off {I:Type} [Fintype I] [DecidableEq I] (S:Finset I) (X:I→Type)
    (w:∀ i:↥S,X i.val→ℝ) (i:I) (hi:i∉S) (x:X i):
    padIndexedFunctions S X w i x=0:=by simp [padIndexedFunctions,hi]

theorem pad_indexed_functions_bounds {I:Type} [Fintype I] [DecidableEq I] (S:Finset I) (X:I→Type)
    (w:∀ i:↥S,X i.val→ℝ) (C:I→ℝ) (hC:∀ i,0≤C i)
    (hw:∀ i x,0≤w i x ∧ w i x≤C i.val):
    ∀ i x,0≤padIndexedFunctions S X w i x ∧ padIndexedFunctions S X w i x≤C i:=by
  intro i x
  by_cases hi:i∈S
  · simpa only [padIndexedFunctions, dif_pos hi] using hw ⟨i,hi⟩ x
  · simp only [padIndexedFunctions,dif_neg hi];exact ⟨le_refl 0,hC i⟩

theorem pad_indexed_functions_sum {I X:Type} [Fintype I] [DecidableEq I] (S:Finset I)
    (w:↥S→X→ℝ) (x:X):
    (∑ i:I,padIndexedFunctions S (fun _=>X) w i x)=∑ i:↥S,w i x:=by
  symm
  calc
    (∑ i:↥S,w i x) = ∑ i:↥S,padIndexedFunctions S (fun _=>X) w i.val x := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (pad_indexed_functions_on S (fun _=>X) w i x).symm
    _ = ∑ i∈S,padIndexedFunctions S (fun _=>X) w i x := by
      exact Finset.sum_coe_sort S (fun i=>padIndexedFunctions S (fun _=>X) w i x)
    _ = ∑ i:I,padIndexedFunctions S (fun _=>X) w i x := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro i _ hi
      exact pad_indexed_functions_off S (fun _=>X) w i hi x
theorem pad_indexed_functions_pointwise_bounds {I:Type} [Fintype I] [DecidableEq I] (S:Finset I) (X:I→Type)
    (w:∀ i:↥S,X i.val→ℝ) (C:∀ i,X i→ℝ) (hC:∀ i x,0≤C i x)
    (hw:∀ i x,0≤w i x ∧ w i x≤C i.val x):
    ∀ i x,0≤padIndexedFunctions S X w i x ∧ padIndexedFunctions S X w i x≤C i x:=by
  intro i x
  by_cases hi:i∈S
  · simpa only [padIndexedFunctions, dif_pos hi] using hw ⟨i,hi⟩ x
  · simp only [padIndexedFunctions,dif_neg hi];exact ⟨le_refl 0,hC i x⟩

end Oberwolfach
