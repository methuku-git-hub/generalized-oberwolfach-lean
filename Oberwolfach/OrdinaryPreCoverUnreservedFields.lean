module

public import Oberwolfach.OrdinaryUnreservedNearGeometryData
public import Oberwolfach.OrdinaryUnreservedCuts
public import Oberwolfach.OrdinaryUnreservedSpokeDegree
public import Oberwolfach.OrdinaryUnreservedConfigurationCounts
public import Oberwolfach.OrdinaryUnreservedWeightLoads
public import Oberwolfach.OrdinaryUnreservedCutsFromReserve
public import Oberwolfach.OrdinaryUnreservedAfterPhysicalDeletion
public import Oberwolfach.OrdinaryPhysicalUnionDegree

@[expose] public section
/-! Structural packing estimates can be taken from a reference host before
an earlier cover: delete that cover and the sampled reserve together, while
keeping the exact post-cover target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem ordinary_unreserved_fields_from_precover
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω βparent β b B h δ εparent εstar η ξ ζ p ε f binner c L:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U)
    (C:SimpleGraph (V⊕U)) (σ:Sym2 (V⊕U)→Bool)
    (fields:OrdinaryEditedParentFields r hr k α βparent b B h δ εparent P Q F H)
    (geo:OrdinaryUnreservedNearGeometryData r k ω βparent β b B εparent εstar η ξ ζ p ε f binner c
      (Q\C.comap Sum.inl) F (fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u)) X Z σ)
    (hC:∀a,(C.degree a:ℝ)≤L)
    (hscaleV:L+(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card V)
    (hscaleU:L+(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card U):
    let Q':=Q\C.comap Sum.inl;let H':=fun v u=>H v u∧¬C.Adj (Sum.inl v) (Sum.inr u);
    let R:=retainedGraph (ordinaryBoundaryGraph Q' H' X Z) σ;
    Nonempty (OrdinaryEditedParentFields r hr k α β b B (h-ξ-ζ) δ εstar P
      (ordinaryUnreservedRim Q' X R) F (ordinaryUnreservedSpokes H' X Z R)):=by
  intro Q' H' R
  let S:=C⊔R
  letI : DecidableRel S.Adj := fun _ _=>Classical.propDecidable _
  have hres:=ordinary_boundary_reserve_total_degree Q' H' X Z p ε geo.p_nonneg σ geo.reserve_good
  have hsum:=ordinary_physical_union_degree C R L ((p+ε)*Fintype.card (V⊕U)) hC hres
  have hV:∀a,(S.degree a:ℝ)≤ζ*Fintype.card V:=by
    intro a
    convert (hsum a).trans hscaleV using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hU:∀a,(S.degree a:ℝ)≤ζ*Fintype.card U:=by
    intro a
    convert (hsum a).trans hscaleU using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hc:=ordinary_unreserved_cuts Q H fields.orientation X Z S δ h ξ ζ
    geo.positive_V geo.positive_U geo.xi_nonneg geo.zeta_nonneg fields.orientation_graph
    geo.inner_rim_size geo.inner_hub_size_U (fun v=>hV (Sum.inl v)) (fun v=>hU (Sum.inl v))
    (fun u=>hV (Sum.inr u)) fields.rim_cuts fields.spoke_cuts
  have hd:=ordinary_unreserved_spoke_degree H X Z S βparent β ξ ζ fields.spoke_degree geo.inner_hub_size_V
    (fun v=>hV (Sum.inl v)) geo.degree_margin
  have hi:=ordinary_unreserved_configuration_counts P Q F H X Z S r k hr geo.k_lower
    (max (1/2) (cycleThreshold r)) (α/4) βparent β ξ ζ geo.positive_V geo.hub_upper geo.xi_nonneg geo.zeta_nonneg
    geo.inner_rim_size geo.inner_hub_size_V hV fields.isolators fields.transfers geo.isolator_margin geo.transfer_margin
  obtain ⟨weight,hw,hwR,hwS⟩:=ordinary_unreserved_weight_loads Q F H X Z S r hr geo.positive_V geo.hub_upper
    fields.weight b B εparent εstar ξ ζ geo.b_pos geo.B_nonneg geo.xi_nonneg geo.zeta_nonneg
    fields.weight_bounds fields.rim_load fields.spoke_load geo.inner_rim_size geo.inner_hub_size_V hV geo.weight_margin
  have hh:Nonempty (OrdinaryEditedParentFields r hr k α β b B (h-ξ-ζ) δ εstar P
      (ordinaryUnreservedRim Q X S) F (ordinaryUnreservedSpokes H X Z S)):=by
    refine ⟨⟨ordinaryUnreservedOrientation fields.orientation X S,hc.1,hc.2.1,hc.2.2,hd,hi.1,hi.2,weight,hw,hwR,hwS⟩⟩
  have he:=ordinary_unreserved_after_physical_deletion Q H X Z C R
  rw [←he.1,←he.2] at hh
  exact hh
end Oberwolfach
