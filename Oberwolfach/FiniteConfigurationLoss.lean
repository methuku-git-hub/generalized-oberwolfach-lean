module

public import Mathlib.Tactic

@[expose] public section

/-! Counting losses in finite configuration families by explicit failures. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_configuration_loss {A B : Type*} [Fintype A] [Fintype B]
    (good : A → Prop) (f : {a // good a} → B) (hf : Function.Injective f) :
    (Fintype.card A : ℝ)-Fintype.card B≤∑ a,if good a then (0 : ℝ) else 1 := by
  classical
  have hc : (Fintype.card {a // good a} : ℝ)≤Fintype.card B := by
    exact_mod_cast Fintype.card_le_of_injective f hf
  have he : (Fintype.card {a // good a} : ℝ)=∑ a,if good a then (1 : ℝ) else 0 := by
    simp only [Fintype.card_subtype,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [he] at hc
  have hs : (∑ a,if good a then (1 : ℝ) else 0)+(∑ a,if good a then (0 : ℝ) else 1)=Fintype.card A := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ _ : A,(1 : ℝ) := by apply Finset.sum_congr rfl;intro a _;split_ifs <;> norm_num
      _ = _ := by simp
  linarith

theorem finite_exists_indicator_le_sum {I : Type*} [Fintype I]
    (P : I → Prop) : (if ∃ i,P i then (1 : ℝ) else 0)≤∑ i,if P i then 1 else 0 := by
  classical
  split_ifs with hex
  · obtain ⟨i,hi⟩ := hex
    have hh := Finset.single_le_sum (s:=Finset.univ)
      (f:=fun j=>if P j then (1 : ℝ) else 0)
      (fun j _=>by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa only [hi,ite_true] using hh
  · exact Finset.sum_nonneg (fun i _=>by split_ifs <;> norm_num)

end Oberwolfach
