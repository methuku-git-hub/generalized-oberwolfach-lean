module

public import Oberwolfach.OrdinaryNonrootGeometryMargins

@[expose] public section
/-! Separate deterministic numerical margins from the later sampled
boundary-reserve event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

structure OrdinaryNonrootGeometryStatic (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε f binner c:ℝ)
    (X:Finset V) (Z:Finset U):Prop where
  positive_V:0<Fintype.card V
  positive_U:0<Fintype.card U
  hub_lower:ω*Fintype.card V≤Fintype.card U
  hub_upper:Fintype.card U≤Fintype.card V
  xi_nonneg:0≤ξ
  zeta_nonneg:0≤ζ
  p_nonneg:0≤p
  b_pos:0<b
  B_nonneg:0≤B
  k_lower:4≤k
  inner_rim_size:(X.card:ℝ)≤ξ*Fintype.card V
  inner_hub_size_V:(Z.card:ℝ)≤ξ*Fintype.card V
  inner_hub_size_U:(Z.card:ℝ)≤ξ*Fintype.card U
  reserve_scale_V:(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card V
  reserve_scale_U:(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card U
  degree_margin:β+ξ+ζ≤βparent
  isolator_margin:8*((ξ+ζ)*Fintype.card V)≤(βparent-β)*Fintype.card V
  transfer_margin:5*(r:ℝ)^4*((ξ+ζ)*Fintype.card V)≤(βparent-β)*Fintype.card V
  weight_margin:εparent+8*(r:ℝ)^4*B*(ξ+ζ)≤εstar
  balance_margin:f+binner+p*max (f+binner) c+3*ε*Fintype.card (V⊕U)≤η*Fintype.card V

theorem ordinary_nonroot_geometry_with_reserve (r k:ℕ)
    (ω βparent β b B εparent εstar η ξ ζ p ε f binner c:ℝ)
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (m:OrdinaryNonrootGeometryStatic r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c X Z)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z p ε σ):
    OrdinaryNonrootGeometryMargins r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c Q F H X Z σ:=by
  exact ⟨m.positive_V,m.positive_U,m.hub_lower,m.hub_upper,m.xi_nonneg,m.zeta_nonneg,m.p_nonneg,m.b_pos,
    m.B_nonneg,m.k_lower,hgood,m.inner_rim_size,m.inner_hub_size_V,m.inner_hub_size_U,m.reserve_scale_V,
    m.reserve_scale_U,m.degree_margin,m.isolator_margin,m.transfer_margin,m.weight_margin,m.balance_margin⟩
end Oberwolfach
