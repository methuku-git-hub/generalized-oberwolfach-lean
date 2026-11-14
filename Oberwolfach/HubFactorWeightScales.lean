module

public import Oberwolfach.MarkedHubFactor

@[expose] public section

/-! Convert the ambient-order weight bounds to the marked-class scale.
The lower bound uses its supplied positive density; the upper bound uses
that a neighbour class is a subset of the ambient vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem hub_factor_weight_scale (m : ℕ) (n k β b B t : ℝ)
    (hn : 0<n) (hk : 0<k) (hβ : 0<β) (hb : 0≤b) (hB : 0≤B)
    (hkn : k≤n) (hβn : β*n≤k) (ht : b/n^m≤t ∧ t≤B/n^m) :
    (b*β^m)/k^m≤t ∧ t≤B/k^m := by
  constructor
  · apply le_trans _ ht.1
    apply (div_le_div_iff₀ (pow_pos hk _) (pow_pos hn _)).mpr
    have hp := pow_le_pow_left₀ (mul_nonneg hβ.le hn.le) hβn m
    rw [mul_pow] at hp
    nlinarith only [mul_le_mul_of_nonneg_left hp hb]
  · exact ht.2.trans (div_le_div_of_nonneg_left hB (pow_pos hk _) (pow_le_pow_left₀ hk.le hkn _))

end Oberwolfach
