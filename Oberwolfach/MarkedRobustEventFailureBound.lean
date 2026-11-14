module

public import Oberwolfach.MarkedSampledRobustAbsorberSharedChanges

@[expose] public section
/-! The inverse-linear failure probability fits any fixed positive
additional-event budget after choosing the order threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem eventually_marked_robust_event_failure_below (χ:ℝ) (hχ:0<χ):
    ∃ N:ℕ,∀ n:ℕ,N≤n→2/(n:ℝ)≤χ/2:=by
  refine ⟨max 1 ⌈4/χ⌉₊,?_⟩
  intro n hn
  have hnpos:(0:ℝ)<n:=by exact_mod_cast (show 0<n by omega)
  have hbound:4/χ≤(n:ℝ):=(Nat.le_ceil _).trans (by exact_mod_cast (show ⌈4/χ⌉₊≤n by omega))
  have hh:4≤(n:ℝ)*χ:=(div_le_iff₀ hχ).mp hbound
  apply (div_le_iff₀ hnpos).mpr
  nlinarith only [hh]
end Oberwolfach
