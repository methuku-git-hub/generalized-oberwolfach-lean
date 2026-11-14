module

public import Oberwolfach.OrdinaryUnreservedNearBalancePacking
public import Oberwolfach.OrdinaryUnreservedBalanceNearParent
public import Oberwolfach.OrdinaryUnreservedSpokeDegree
public import Oberwolfach.OrdinaryUnreservedConfigurationCounts
public import Oberwolfach.OrdinaryUnreservedWeightLoads

@[expose] public section
/-! Assemble the near-balance packing input on the actual unreserved host.
All structural data belong to the original parent; the same reserve sample is
used in every restriction. The numerical margins remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option synthInstance.maxSize 2048
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

structure OrdinaryUnreservedNearParentData (r:ℕ) (hr:3≤r) (k:ℕ) (α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε f b c:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool) where
  positive_V:0<Fintype.card V
  positive_U:0<Fintype.card U
  hub_lower:ω*Fintype.card V≤Fintype.card U
  hub_upper:Fintype.card U≤Fintype.card V
  xi_nonneg:0≤ξ
  zeta_nonneg:0≤ζ
  p_nonneg:0≤p
  bminus_pos:0<bminus
  bplus_nonneg:0≤bplus
  k_lower:4≤k
  graph_sub:Q≤P\F
  orientation:V→V→ℕ
  orientation_graph:∀x y,orientation x y+orientation y x=if Q.Adj x y then 1 else 0
  rim_cuts:BipartiteLargeCut orientation δ h
  spoke_cuts:BipartiteLargeCut (relationMultiplicity H) δ h
  spoke_degree:∀v,β₀*Fintype.card V≤((Finset.univ.filter (H v)).card:ℝ)
  near_balance:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤f
  inner_balance:∀v,|((spanningRestriction Q X).degree v:ℝ)-
    2*(Finset.univ.filter (fun u=>H v u∧v∈X∧u∈Z)).card|≤b
  cross_balance:∀v∉X,|((Q.neighborFinset v∩X).card:ℝ)-2*(Z.filter (H v)).card|≤c
  isolators:∀x y,Q.Adj x y→β₀*(Fintype.card V:ℝ)^(k-1)≤
    (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k (max (1/2) (cycleThreshold r)) (α/4) x y):ℝ)
  transfers:∀v (i j:{u // H v u}),i.val≠j.val→β₀*(Fintype.card V:ℝ)^(r^2)≤
    (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ)
  weight:OrdinaryWheel Q F H r→ℝ
  weight_bounds:∀W,bminus/(Fintype.card V:ℝ)^(r-1)≤weight W ∧ weight W≤bplus/(Fintype.card V:ℝ)^(r-1)
  rim_load:∀x y,Q.Adj x y→|ordinaryRimLoad weight x y-1|≤ε₀
  spoke_load:∀v u,H v u→|ordinarySpokeLoad weight v u-1|≤ε₀
  reserve_good:OrdinaryBoundaryReserveGood Q H X Z p ε σ
  inner_rim_size:(X.card:ℝ)≤ξ*Fintype.card V
  inner_hub_size_V:(Z.card:ℝ)≤ξ*Fintype.card V
  inner_hub_size_U:(Z.card:ℝ)≤ξ*Fintype.card U
  reserve_scale_V:(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card V
  reserve_scale_U:(p+ε)*Fintype.card (V⊕U)≤ζ*Fintype.card U
  degree_margin:β+ξ+ζ≤β₀
  isolator_margin:8*((ξ+ζ)*Fintype.card V)≤(β₀-β)*Fintype.card V
  transfer_margin:5*(r:ℝ)^4*((ξ+ζ)*Fintype.card V)≤(β₀-β)*Fintype.card V
  weight_margin:ε₀+8*(r:ℝ)^4*bplus*(ξ+ζ)≤εstar
  balance_margin:f+b+p*max (f+b) c+3*ε*Fintype.card (V⊕U)≤η*Fintype.card V

theorem ordinary_unreserved_packing_data_from_near_parent
    (r:ℕ) (hr:3≤r) (k:ℕ) (α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε f b c:ℝ)
    (P Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (σ:Sym2 (V⊕U)→Bool)
    (d:OrdinaryUnreservedNearParentData r hr k α ω β₀ β bminus bplus h δ ε₀ εstar η ξ ζ p ε f b c P Q F H X Z σ):
    let R:=retainedGraph (ordinaryBoundaryGraph Q H X Z) σ;
    Nonempty (OrdinaryNearBalancePackingData r hr k α ω β bminus bplus (h-ξ-ζ) δ εstar η P
      (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R)):=by
  intro R
  have hdeg:∀w,(R.degree w:ℝ)≤ζ*Fintype.card V:=by
    intro w
    exact (ordinary_boundary_reserve_total_degree Q H X Z p ε d.p_nonneg σ d.reserve_good w).trans d.reserve_scale_V
  have hc:=ordinary_unreserved_cuts_from_reserve Q H d.orientation X Z σ δ h ξ ζ p ε
    d.positive_V d.positive_U d.xi_nonneg d.zeta_nonneg d.p_nonneg d.reserve_good
    d.reserve_scale_V d.reserve_scale_U d.orientation_graph d.inner_rim_size d.inner_hub_size_U d.rim_cuts d.spoke_cuts
  have hd:=ordinary_unreserved_spoke_degree H X Z R β₀ β ξ ζ d.spoke_degree d.inner_hub_size_V
    (fun v=>hdeg (Sum.inl v)) d.degree_margin
  have hb:=ordinary_unreserved_balance_from_reserve_near_parent Q H X Z p ε f b c η d.p_nonneg σ d.reserve_good
    d.near_balance d.inner_balance d.cross_balance d.balance_margin
  have hi:=ordinary_unreserved_configuration_counts P Q F H X Z R r k hr d.k_lower
    (max (1/2) (cycleThreshold r)) (α/4) β₀ β ξ ζ d.positive_V d.hub_upper d.xi_nonneg d.zeta_nonneg
    d.inner_rim_size d.inner_hub_size_V hdeg d.isolators d.transfers d.isolator_margin d.transfer_margin
  obtain ⟨w,hw,hwR,hwS⟩:=ordinary_unreserved_weight_loads Q F H X Z R r hr d.positive_V d.hub_upper
    d.weight bminus bplus ε₀ εstar ξ ζ d.bminus_pos d.bplus_nonneg d.xi_nonneg d.zeta_nonneg
    d.weight_bounds d.rim_load d.spoke_load d.inner_rim_size d.inner_hub_size_V hdeg d.weight_margin
  refine ⟨⟨d.hub_lower,d.hub_upper,?_,ordinaryUnreservedOrientation d.orientation X R,hc.1,hc.2.1,?_,hd,hb,hi.1,hi.2,w,hw,hwR,hwS⟩⟩
  · intro x y hxy
    apply d.graph_sub
    exact hxy.1.1
  · convert hc.2.2 using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
