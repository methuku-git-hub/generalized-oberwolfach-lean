module

public import Oberwolfach.LongOriginalRegularJointWeights

@[expose] public section
/-! The even long seed selected from the original host has exactly the
length parameters used by the successor matching construction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_original_seed_length_parameters
    (m:ℕ) (hm:7≤m) (heven:Even (m+1)):
    ∃r k₀:ℕ,2≤r ∧ m=r+4 ∧ r+4+1=(k₀+2)*2 ∧ 7≤r+4:=by
  obtain ⟨t,ht⟩:=heven
  refine ⟨m-4,t-2,?_,?_,?_,?_⟩ <;> omega
end Oberwolfach
