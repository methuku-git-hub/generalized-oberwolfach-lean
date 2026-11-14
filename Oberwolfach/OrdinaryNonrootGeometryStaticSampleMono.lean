module

public import Oberwolfach.OrdinaryNonrootGeometryStatic

@[expose] public section
/-! Later fresh-sampling choices may shrink both the sampling probability
and its error while retaining the already chosen static parent geometry. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_nonroot_geometry_static_sample_mono
    (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε f binner c p' ε':ℝ)
    (X:Finset V) (Z:Finset U)
    (h:OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c X Z)
    (hp':0≤p') (hpp:p'≤p) (hεε:ε'≤ε) (hc:0≤c):
    OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p' ε' f binner c X Z :=by
  have hn:0≤(Fintype.card (V⊕U):ℝ):=by positivity
  have hsum:p'+ε'≤p+ε:=add_le_add hpp hεε
  have hscale: (p'+ε')*Fintype.card (V⊕U)≤(p+ε)*Fintype.card (V⊕U):=
    mul_le_mul_of_nonneg_right hsum hn
  have hmax:0≤max (f+binner) c:=hc.trans (le_max_right _ _)
  have hpmax:p'*max (f+binner) c≤p*max (f+binner) c:=mul_le_mul_of_nonneg_right hpp hmax
  have herr:ε'*Fintype.card (V⊕U)≤ε*Fintype.card (V⊕U):=mul_le_mul_of_nonneg_right hεε hn
  refine ⟨h.positive_V,h.positive_U,h.hub_lower,h.hub_upper,h.xi_nonneg,h.zeta_nonneg,hp',h.b_pos,h.B_nonneg,h.k_lower,
    h.inner_rim_size,h.inner_hub_size_V,h.inner_hub_size_U,hscale.trans h.reserve_scale_V,hscale.trans h.reserve_scale_U,
    h.degree_margin,h.isolator_margin,h.transfer_margin,h.weight_margin,?_⟩
  linarith only [h.balance_margin,hpmax,herr]
end Oberwolfach
