module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! Total number of source vertices across the prescribed family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem prescribed_embedding_total_size {I:Type} [Fintype I] (q:I→ℕ) (δ n:ℝ)
    (hδ:0≤δ) (hn:0≤n) (hI:(Fintype.card I:ℝ)≤n)
    (hq:∀ i,(q i:ℝ)≤δ*n):
    ((∑ i,q i:ℕ):ℝ)≤δ*n^2 := by
  have hsum:(∑ i,(q i:ℝ))≤(Fintype.card I:ℝ)*(δ*n):=by
    calc
      _ ≤ ∑ _i:I,δ*n:=Finset.sum_le_sum (fun i _=>hq i)
      _ = _ := by simp
  have hh:=mul_le_mul_of_nonneg_right hI (mul_nonneg hδ hn)
  push_cast
  nlinarith
end Oberwolfach
