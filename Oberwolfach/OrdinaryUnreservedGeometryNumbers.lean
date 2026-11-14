module

public import Oberwolfach.OrdinaryUnreservedGeometryData

@[expose] public section
/-! Numeric and set-size part of reserve geometry; the sample supplies
the balance profiles separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

structure OrdinaryUnreservedGeometryNumbers (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε bound:ℝ)
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
  balance_margin:bound+p*max bound bound+3*ε*Fintype.card (V⊕U)≤η*Fintype.card V

theorem ordinary_unreserved_geometry_from_balance_profiles
    (r k:ℕ) (ω βparent β b B εparent εstar η ξ ζ p ε bound:ℝ)
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (num:OrdinaryUnreservedGeometryNumbers r k ω βparent β b B εparent εstar η ξ ζ p ε bound X Z)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hinner:∀v,|((spanningRestriction Q X).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤bound)
    (hcross:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤bound)
    (hgood:OrdinaryBoundaryReserveGood Q H X Z p ε σ):
    OrdinaryUnreservedGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε bound bound Q F H X Z σ:=by
  exact ⟨num.positive_V,num.positive_U,num.hub_lower,num.hub_upper,num.xi_nonneg,num.zeta_nonneg,
    num.p_nonneg,num.b_pos,num.B_nonneg,num.k_lower,hbal,hinner,hcross,hgood,num.inner_rim_size,
    num.inner_hub_size_V,num.inner_hub_size_U,num.reserve_scale_V,num.reserve_scale_U,num.degree_margin,
    num.isolator_margin,num.transfer_margin,num.weight_margin,num.balance_margin⟩
end Oberwolfach
