module

public import Oberwolfach.OrdinaryNonrootGeometryStatic

@[expose] public section
/-! Shrinking all three deterministic loss budgets preserves the static
reference geometry. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_nonroot_geometry_static_loss_mono
    (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε f binner c f' binner' c':ℝ)
    (X:Finset V) (Z:Finset U)
    (h:OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c X Z)
    (hf:f'≤f) (hb:binner'≤binner) (hc:c'≤c):
    OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p ε f' binner' c' X Z :=by
  have hsum:f'+binner'≤f+binner:=add_le_add hf hb
  have hmax:max (f'+binner') c'≤max (f+binner) c:=max_le_max hsum hc
  have hmul:p*max (f'+binner') c'≤p*max (f+binner) c:=mul_le_mul_of_nonneg_left hmax h.p_nonneg
  refine ⟨h.positive_V,h.positive_U,h.hub_lower,h.hub_upper,h.xi_nonneg,h.zeta_nonneg,h.p_nonneg,h.b_pos,h.B_nonneg,h.k_lower,
    h.inner_rim_size,h.inner_hub_size_V,h.inner_hub_size_U,h.reserve_scale_V,h.reserve_scale_U,
    h.degree_margin,h.isolator_margin,h.transfer_margin,h.weight_margin,?_⟩
  linarith only [h.balance_margin,hsum,hmul]
end Oberwolfach
