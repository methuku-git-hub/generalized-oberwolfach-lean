module

public import Mathlib.Tactic

@[expose] public section
/-! The marked preparation length and the reference theorem's two indices
name the same even cycle and the same number of ordinary positions. -/
set_option autoImplicit false
namespace Oberwolfach

theorem marked_preparation_reference_indices (m:ℕ) (hm:6≤m) (heven:Even (m+1)):
    ∃ r k₀:ℕ,2≤r ∧ r+4=m ∧ r+4+1=(k₀+2)*2:=by
  obtain ⟨k,hk⟩:=heven
  refine ⟨m-4,k-2,?_,?_,?_⟩ <;> omega
end Oberwolfach
