module

public import Oberwolfach.MarkedInitialIndexCardBounds

@[expose] public section
/-! Positive initial index density gives a linear number of hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_initial_index_card_lower {V U:Type} [Fintype V] [Fintype U]
    (D:ℕ) (hn:0<Fintype.card V) (α ρ₀:ℝ) (hα:0<α) (hρ₀:0<ρ₀)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ))
    (hρlo:ρ₀≤ initialIndexDensity U D):
    (ρ₀/4)*(Fintype.card V:ℝ)≤Fintype.card U:=by
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hDp:(0:ℝ)<D:=lt_of_lt_of_le (by positivity) hD
  have hρD:ρ₀*(D:ℝ)≤2*Fintype.card U:=by
    have hh:=hρlo
    unfold initialIndexDensity at hh
    exact (le_div_iff₀ hDp).mp hh
  have hhalf:(Fintype.card V:ℝ)/2≤D:=by nlinarith
  have hh:=mul_le_mul_of_nonneg_left hhalf hρ₀.le
  nlinarith
end Oberwolfach
