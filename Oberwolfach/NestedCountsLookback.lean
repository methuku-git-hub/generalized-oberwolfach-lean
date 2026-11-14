module

public import Oberwolfach.NestedCounts

@[expose] public section
/-! Telescoping remains valid for any fixed number of earlier root levels. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem nested_normalized_count_estimate_lookback {V:Type*} (B:ℕ→Finset V)
    (A:V→Finset V) (e:ℕ→ℝ) (k t:ℕ)
    (hsub:∀i<k,B (i+1)⊆B i)
    (hstep:∀i<k,∀x∈B (i-t),
      |((A x∩B (i+1)).card:ℝ)/(B (i+1)).card-
        ((A x∩B i).card:ℝ)/(B i).card|≤e i)
    {i:ℕ} (hi:i≤k) {x:V} (hx:x∈B (i-(t+1))):
    |((A x∩B i).card:ℝ)/(B i).card-
      ((A x∩B 0).card:ℝ)/(B 0).card|≤∑j∈Finset.range i,e j :=by
  apply abs_chain_difference_bound (fun j=>((A x∩B j).card:ℝ)/(B j).card) e i
  intro j hj
  apply hstep j (by omega)
  exact finset_chain_subset B k hsub (by omega:j-t ≤ i-(t+1)) (by omega) hx
end Oberwolfach
