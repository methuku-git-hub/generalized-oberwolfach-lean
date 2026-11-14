module

public import Oberwolfach.OrdinaryUnreservedPackingNearParent
public import Oberwolfach.OrdinaryEditedParentFields

@[expose] public section
/-! Reserve geometry, balance and margins independent of the construction
of the edited parent's structural fields. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

structure OrdinaryUnreservedNearGeometryData (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε f binner c:ℝ)
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool):Prop where
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
  near_balance:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤f
  inner_balance:∀v,|((spanningRestriction Q X).degree v:ℝ)-
    2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤binner
  cross_balance:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c
  reserve_good:OrdinaryBoundaryReserveGood Q H X Z p ε σ
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

theorem ordinary_unreserved_near_parent_data_from_edited_fields
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (hQP:Q≤P\F) (fields:OrdinaryEditedParentFields r hr k α βparent b B h δ εparent P Q F H)
    (geo:OrdinaryUnreservedNearGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c Q F H X Z σ):
    Nonempty (OrdinaryUnreservedNearParentData r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c P Q F H X Z σ):=by
  exact ⟨⟨geo.positive_V,geo.positive_U,geo.hub_lower,geo.hub_upper,geo.xi_nonneg,geo.zeta_nonneg,
    geo.p_nonneg,geo.b_pos,geo.B_nonneg,geo.k_lower,hQP,fields.orientation,fields.orientation_graph,
    fields.rim_cuts,fields.spoke_cuts,fields.spoke_degree,geo.near_balance,geo.inner_balance,geo.cross_balance,
    fields.isolators,fields.transfers,fields.weight,fields.weight_bounds,fields.rim_load,fields.spoke_load,
    geo.reserve_good,geo.inner_rim_size,geo.inner_hub_size_V,geo.inner_hub_size_U,geo.reserve_scale_V,
    geo.reserve_scale_U,geo.degree_margin,geo.isolator_margin,geo.transfer_margin,geo.weight_margin,geo.balance_margin⟩⟩
end Oberwolfach
