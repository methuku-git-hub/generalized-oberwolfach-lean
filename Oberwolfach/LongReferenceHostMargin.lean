module

public import Oberwolfach.LongRegularHostNumericInputs

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

/-- The reference event's upper bound on its density margin follows from
regularity and the matching construction's host-density hypothesis. -/
theorem long_reference_host_margin_le_half
    {V:Type} [Fintype V] (G:SimpleGraph V) (D:ℕ) (α:ℝ)
    (hreg:G.IsRegularOfDegree D) (hn:0<Fintype.card V)
    (hmin:(1/2+α)*Fintype.card V≤(D:ℝ)) : α≤1/2 := by
  have hDnat:D≤Fintype.card V:=regular_degree_le_card hreg hn
  have hD:(D:ℝ)≤Fintype.card V:=by exact_mod_cast hDnat
  have hnR:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  by_contra h
  have hh:0<(α-1/2)*(Fintype.card V:ℝ):=mul_pos (by linarith) hnR
  nlinarith
end Oberwolfach
