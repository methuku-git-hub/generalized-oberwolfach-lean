module

public import Oberwolfach.ClassFrequencyDomainError

@[expose] public section
/-! Passing from an included set to its complement preserves absolute error. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_complement_approximation {n:ℕ} (T:Set (Fin n)) (target err:ℝ)
    (h:|((Fintype.card T:ℕ):ℝ)-target|≤err):
    |((Fintype.card {v:Fin n // v∉T}:ℕ):ℝ)-((n:ℝ)-target)|≤err :=by
  have ht:Fintype.card T≤n:=by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (fun x:T=>x.val) Subtype.val_injective
  have hc:((Fintype.card {v:Fin n // v∉T}:ℕ):ℝ)=(n:ℝ)-((Fintype.card T:ℕ):ℝ):=by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Nat.cast_sub ht]
  rw [hc]
  have heq:(n:ℝ)-((Fintype.card T:ℕ):ℝ)-((n:ℝ)-target)=-(((Fintype.card T:ℕ):ℝ)-target):=by ring
  rw [heq,abs_neg]
  exact h
end Oberwolfach
