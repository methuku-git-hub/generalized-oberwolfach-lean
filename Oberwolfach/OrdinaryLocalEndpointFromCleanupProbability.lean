module

public import Oberwolfach.OrdinaryLocalEndpointProbabilityAmbient
public import Oberwolfach.OrdinaryLocalEndpointGeometryFromCleanup
public import Oberwolfach.OrdinaryLocalEndpointMeanMargins
public import Oberwolfach.OrdinaryLocalEndpointErrorMargins
public import Oberwolfach.PhysicalBoundaryFullClassAfterPacking
public import Oberwolfach.PhysicalWheelFamilies
public import Oberwolfach.MappedFactorGraph

@[expose] public section
/-! Endpoint pairings for the actual cleanup profile, using a fixed inner
physical domain and the original ambient edge coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_local_endpoint_from_cleanup_probability
    (p₀ κ:ℝ) (hp₀:0<p₀) (hp₀1:p₀≤1) (hκ:0<κ) (hκ1:κ≤1):
    ∃a η ζ δ:ℝ,0<a ∧ a≤1 ∧ 0<η ∧ 0<ζ ∧ 0<δ ∧
    ∀(b q:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (pR pH density tR tH L βe βh:ℝ) (σ:RawWheelOutcome V U Γ Color),
    OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH L βe βh s j σ→
    A.Nonempty→N≤(ordinaryPhysicalInnerDomain A B).card→
    Fintype.card {v:V // v∉A}≤(ordinaryPhysicalInnerDomain A B).card^2→
    κ*A.card≤(B.card:ℝ)→B.card≤A.card→p₀≤pR→p₀≤pH→pH≤1→
    0≤tR→0≤tH→0≤L→tR+L≤δ*A.card→tH+L≤δ*A.card→
    (∀v,F.degree v≤b)→
    let S:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U);
    let R:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRowSet H A B i).image (Sum.inr:U→V⊕U);
    let G:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B);
    let K:=ordinaryPhysicalGraph F (fun _ _=>False);
    let g:=fun i:{v:V // v∉A}=>physicalIncidentCoin (Sum.inl i.val:V⊕U);
    1-1/((ordinaryPhysicalInnerDomain A B).card:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (OrdinaryLocalEndpointEvent G K (ordinaryPhysicalInnerDomain A B) S R g p ζ):=by
  obtain ⟨a,δmean,ha,ha1,hδmean,hmean⟩:=ordinary_local_endpoint_mean_margins p₀ κ hp₀ hp₀1 hκ hκ1
  obtain ⟨η,ζ,hη,hζ,hprob⟩:=ordinary_local_endpoint_probability_ambient p₀ a hp₀ hp₀1 ha ha1
  obtain ⟨δerr,hδerr,herr⟩:=ordinary_local_endpoint_error_margins a η ha hη
  refine ⟨a,η,ζ,min δmean δerr,ha,ha1,hη,hζ,lt_min hδmean hδerr,?_⟩
  intro b q p hp hp1
  obtain ⟨N,hN⟩:=hprob b q p hp hp1
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A B π d j s pR pH density tR tH L βe βh σ profile
    hA hn houter hBA hBA' hpR hpH hpH1 htR htH hL hcostR hcostH hF S R G K g
  have hAc:0≤(A.card:ℝ):=by positivity
  have hmeanR:tR+L≤δmean*A.card:=hcostR.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hAc)
  have hmeanH:tH+L≤δmean*A.card:=hcostH.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) hAc)
  have herrR:tR+L≤δerr*A.card:=hcostR.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hAc)
  have herrH:tH+L≤δerr*A.card:=hcostH.trans
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hAc)
  have hBAreal:(B.card:ℝ)≤A.card:=by exact_mod_cast hBA'
  have hm:=hmean A.card B.card pR pH density (tR+L) (tH+L) hAc hBA hBAreal hpR hpH
    profile.density_large hmeanR hmeanH
  have hc:=ordinary_physical_inner_domain_card A B
  have hr:a*(ordinaryPhysicalInnerDomain A B).card+tR+L≤pR*density*A.card:=by
    rw [hc,Nat.cast_add]
    linarith only [hm.1]
  have hh:a*(ordinaryPhysicalInnerDomain A B).card+tH+L≤pH*B.card:=by
    rw [hc,Nat.cast_add]
    linarith only [hm.2]
  have hs:=ordinary_local_endpoint_sizes_from_cleanup P Q F H A B (ordinaryPhysicalInnerDomain A B)
    π d j s pR pH density tR tH L βe βh a σ profile hA hr hh
  have hAT:(A.card:ℝ)≤(ordinaryPhysicalInnerDomain A B).card:=by
    rw [hc,Nat.cast_add]
    have hB:(0:ℝ)≤B.card:=by positivity
    linarith only [hB]
  have he (x:V):=(herr A.card (ordinaryPhysicalInnerDomain A B).card pH tR tH L
    (A∩Q.neighborFinset x).card (B.filter (H x)).card hAc hAT profile.spoke_nonneg hpH1 htR htH hL
    herrR herrH (hs.1 x) (hs.2 x))
  have geom:=ordinary_local_endpoint_geometry_from_cleanup P Q F H A B π d j s pR pH density tR tH L βe βh a η σ
    profile hA hs.1 hs.2 (fun x=>(he x).1) (fun x=>(he x).2.1) (fun x=>(he x).2.2)
  have hK:∀w:V⊕U,K.degree w≤b:=by
    intro w
    change (ordinaryPhysicalGraph F (fun _ _=>False)).degree w≤b
    rw [←graph_map_inl_physical]
    simpa only [←SimpleGraph.ncard_neighborSet] using
      graph_map_degree_bound F (Function.Embedding.inl:V↪V⊕U) b hF w
  exact hN (V⊕U) {v:V // v∉A} (Sym2 (V⊕U)) G K (ordinaryPhysicalInnerDomain A B) S R g
    (fun _=>pH) hn houter geom.1 geom.2.1 geom.2.2.1 (fun _=>⟨hpH,hpH1⟩) geom.2.2.2.1
    hK geom.2.2.2.2.1 geom.2.2.2.2.2.1 geom.2.2.2.2.2.2
end Oberwolfach
