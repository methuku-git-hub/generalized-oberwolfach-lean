module

public import Oberwolfach.PreparationBalancedMeans

@[expose] public section
/-! Combine the marked contribution with all ordinary contributions on one
outcome, preserving each fixed coefficient and each error term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem preparation_concentrated_balanced_sum {I:Type} [Fintype I]
    (τ a m x t:ℝ) (b z means errors:I→ℝ)
    (hbalance:a+∑ i,b i=1) (hm:(1-τ)*a≤m ∧ m≤(1+τ)*a)
    (hmeans:∀ i,(1-τ)*b i≤means i ∧ means i≤(1+τ)*b i)
    (hx:|x-m|<t) (hz:∀ i,|z i-means i|<errors i):
    |x+∑ i,z i-1|<t+(∑ i,errors i)+τ:=by
  have hmean:=preparation_balanced_means τ a m b means hbalance hm hmeans
  have hmeanerr:|m+∑ i,means i-1|≤τ:=abs_le.mpr ⟨by linarith [hmean.1],by linarith [hmean.2]⟩
  have hobs:|x+∑ i,z i-(m+∑ i,means i)|≤|x-m|+∑ i,|z i-means i|:=by
    calc
      _ = |(x-m)+∑ i,(z i-means i)|:=by rw [Finset.sum_sub_distrib];congr 1;ring
      _ ≤ |x-m|+|∑ i,(z i-means i)|:=abs_add_le _ _
      _ ≤ _:=by
        simpa only [add_comm] using add_le_add_left (Finset.abs_sum_le_sum_abs (fun i=>z i-means i) Finset.univ) |x-m|
  have hsum:(∑ i,|z i-means i|)≤∑ i,errors i:=Finset.sum_le_sum (fun i _=>(hz i).le)
  calc
    _ ≤ |x+∑ i,z i-(m+∑ i,means i)|+|m+∑ i,means i-1|:=abs_sub_le _ _ _
    _ ≤ |x-m|+(∑ i,|z i-means i|)+τ:=by linarith [hobs,hmeanerr]
    _ < t+(∑ i,errors i)+τ:=by linarith [hx,hsum]
end Oberwolfach
