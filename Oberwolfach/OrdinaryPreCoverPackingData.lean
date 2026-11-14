module

public import Oberwolfach.OrdinaryPreCoverUnreservedFields
public import Oberwolfach.OrdinaryUnreservedBalanceNearParent
public import Oberwolfach.OrdinaryNearBalancePackingData

@[expose] public section
/-! The actual post-cover unreserved host has the near-balance packing
input when the pre-cover structural data and explicit margins hold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_precover_unreserved_packing_data
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (hQP:Q≤P\F)
    (fields:OrdinaryEditedParentFields r hr k α βparent b B h δ εparent P Q F H)
    (geo:OrdinaryUnreservedNearGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
      (Q\C.comap Sum.inl) F (fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u)) X Z σ)
    (hC:∀a,(C.degree a:ℝ)≤L)
    (hscaleV:L+(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card V)
    (hscaleU:L+(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card U):
    let Q':=Q\C.comap Sum.inl;let H':=fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u);
    let R:=retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ;
    Nonempty (OrdinaryNearBalancePackingData r hr k α ω β b B (h-ξ-ζ) δ εstar η P
      (ordinaryUnreservedRim Q' X R) F (ordinaryUnreservedSpokes H' X Z R)):=by
  intro Q' H' R
  obtain ⟨d⟩:=ordinary_unreserved_fields_from_precover r hr k α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L
    P Q F H X Z C σ fields geo hC hscaleV hscaleU
  have hb:=ordinary_unreserved_balance_from_reserve_near_parent Q' H' X Z p ε f binner c η
    geo.p_nonneg σ geo.reserve_good geo.near_balance geo.inner_balance geo.cross_balance geo.balance_margin
  refine ⟨⟨geo.hub_lower,geo.hub_upper,?_,d.orientation,d.orientation_graph,d.rim_cuts,d.spoke_cuts,
    d.spoke_degree,hb,d.isolators,d.transfers,d.weight,d.weight_bounds,d.rim_load,d.spoke_load⟩⟩
  intro x y hxy
  apply hQP
  exact hxy.1.1.1
end Oberwolfach
