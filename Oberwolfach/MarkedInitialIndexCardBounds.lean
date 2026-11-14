module

public import Oberwolfach.MarkedActualParentFullNeighbourhoodEvent

@[expose] public section
/-! Index-size hypotheses needed by the expanded preparation estimates
follow from the regular host and its positive index density. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_initial_index_card_bounds {V U:Type} [Fintype V] [Fintype U]
    (G:SimpleGraph V) (D:ℕ) (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (α ρ₀:ℝ) (hα:0<α) (hρ₀:0<ρ₀)
    (hD:(1/2+α)*Fintype.card V≤(D:ℝ))
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1):
    0<Fintype.card U ∧ Fintype.card U≤Fintype.card V:=by
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hDp:(0:ℝ)<D:=lt_of_lt_of_le (by positivity) hD
  have hDle:D≤Fintype.card V:=regular_degree_le_card hreg hn
  have hDr:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hDle
  have hupper:(2:ℝ)*Fintype.card U≤D:=by
    have hh:=hρhi
    unfold initialIndexDensity at hh
    exact (div_le_one hDp).mp hh
  have hUpos:(0:ℝ)<Fintype.card U:=by
    have hh:0< initialIndexDensity U D:=lt_of_lt_of_le hρ₀ hρlo
    unfold initialIndexDensity at hh
    have hh':0<(2:ℝ)*Fintype.card U:=(div_pos_iff_of_pos_right hDp).mp hh
    linarith
  constructor
  · exact_mod_cast hUpos
  · have hh:(Fintype.card U:ℝ)≤Fintype.card V:=by linarith
    exact_mod_cast hh
end Oberwolfach
