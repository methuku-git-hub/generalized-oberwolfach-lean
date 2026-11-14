module

public import Oberwolfach.OrdinarySmallRootDensity

@[expose] public section
/-! Positive relative hub density gives a hub whenever the vertex set is nonempty. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem ordinary_positive_hub_density_nonempty (V U:Type) [Fintype V] [Fintype U]
    (ω:ℝ) (hω:0<ω) (hn:0<Fintype.card V)
    (hU:ω*Fintype.card V≤(Fintype.card U:ℝ)):Nonempty U := by
  have hv:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hu:0<(Fintype.card U:ℝ):=(mul_pos hω hv).trans_le hU
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hu)
end Oberwolfach
