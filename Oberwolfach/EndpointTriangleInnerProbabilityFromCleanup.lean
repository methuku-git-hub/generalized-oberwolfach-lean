module

public import Oberwolfach.EndpointTriangleInnerFactorProbability
public import Oberwolfach.EndpointPhysicalWeightInnerScale
public import Oberwolfach.EndpointNeighborhoodsFromCleanupInnerScale
public import Oberwolfach.EndpointPhysicalPotentialEvent
public import Oberwolfach.PhysicalBoundaryFullClassAfterPacking

@[expose] public section
/-! The endpoint triangle parent can be selected before the vortex size:
its constants use the original lower bounds and the actual inner domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_triangle_inner_probability_from_cleanup
    (κ pmin:ℝ) (hκ:0<κ) (hpmin:0<pmin):
    ∃εfactor η ζ εrows:ℝ,0<εfactor ∧ 0<η ∧ 0<ζ ∧ 0<εrows ∧
    ∀(p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃N:ℕ,
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    ∀(P Q F:SimpleGraph V) (H:V→U→Prop) (A:Finset V) (B:Finset U)
      (π:Equiv.Perm V) (d:ℕ) (j:Color) (s:U→Color→ℝ)
      (weight:V→Sym2 (V⊕U)→ℝ) (pR pH density tR tH tP L Ledit βe βh δ:ℝ)
      (σ:RawWheelOutcome V U Γ Color),
    N≤A.card→Fintype.card {v:V // v∉A}≤A.card^2→
    OrdinaryCleanupParentProfiles P Q F H π d A B pR pH density tR tH Ledit βe βh s j σ→
    RawOrdinaryRows P π d 3 A pR s j tR σ→
    EndpointPhysicalParentWeights P A Aᶜ weight→
    EndpointPhysicalPotentialEvent P F A B Aᶜ π d j weight pR pH tP σ→
    EndpointPhysicalEditedConditions P Q F H A B Aᶜ π d j κ pmin pR pH L Ledit δ σ→
    tR+4*Ledit≤εrows*A.card→tH+3*Ledit≤εrows*B.card→
    L≤(A.card:ℝ)/24→L≤εfactor*A.card→
    δ+(2*40+(1+2*40)/(2*κ*pmin))*L/A.card+
      (tP+10*(40/(κ*pmin^5))*Ledit/A.card)≤η→
    (∀x∉A,∀v∈insert x A,(3/4:ℝ)*A.card≤((A∩P.neighborFinset v).card:ℝ))→
    let Pinner:=ordinaryPhysicalGraph (spanningRestriction Q A) (fun v u=>H v u∧v∈A∧u∈B);
    let Fphys:=ordinaryPhysicalGraph F (fun _ _=>False);
    let S:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRimSet Q A i).image (Sum.inl:V→V⊕U);
    let T:=fun i:{v:V // v∉A}=>(ordinaryBoundaryRowSet H A B i).image (Sum.inr:U→V⊕U);
    let W:Type:={w:V⊕U // w∈ordinaryPhysicalInnerDomain A B};
    1-1/(Fintype.card W:ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (EndpointTriangleNormalizedFactorEvent Pinner Fphys S T
          (fun i=>physicalIncidentCoin (Sum.inl i.val)) p ζ):=by
  let γ:ℝ:=endpointCountCoefficient pmin κ/4
  let b:ℝ:=1/30
  let Bweight:ℝ:=40/(κ*pmin^5)
  let εrows:ℝ:=min (pmin^4/16) (pmin^3/2)
  have hγ:0<γ:=by dsimp [γ];have h:=endpointCountCoefficient_pos pmin κ hpmin hκ;positivity
  have hb:0<b:=by dsimp [b];norm_num
  have hB:0≤Bweight:=by dsimp [Bweight];positivity
  have hrows:0<εrows:=by dsimp [εrows];positivity
  obtain ⟨εfactor,η,ζ,hεfactor,hη,hζ,hbase⟩:=endpoint_triangle_inner_factor_probability γ b Bweight hγ hb hB
  refine ⟨εfactor,η,ζ,εrows,hεfactor,hη,hζ,hrows,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P Q F H A B π d j s weight pR pH density tR tH tP L Ledit βe βh δ σ
    hn hJ profile deep parent event geom hrow hindex hLA hLfactor herr hdeg Pinner Fphys S T W
  let e:W↪V⊕U:=Function.Embedding.subtype (fun w=>w∈ordinaryPhysicalInnerDomain A B)
  have hA:A.Nonempty:=Finset.card_pos.mp geom.row_pos
  have hW:Fintype.card W=(ordinaryPhysicalInnerDomain A B).card:=by simp only [W,Fintype.card_coe]
  have hWA:Fintype.card W=A.card+B.card:=by rw [hW,ordinary_physical_inner_domain_card]
  have hnW:N≤Fintype.card W:=by omega
  have hJW:Fintype.card {v:V // v∉A}≤(Fintype.card W)^2:=by
    have hh:A.card≤Fintype.card W:=by omega
    exact hJ.trans (Nat.pow_le_pow_left hh _)
  have ha:0<(A.card:ℝ):=by exact_mod_cast geom.row_pos
  have han:(A.card:ℝ)≤Fintype.card W:=by exact_mod_cast (show A.card≤Fintype.card W by omega)
  have hsize:(Fintype.card W:ℝ)≤2*(A.card:ℝ):=by
    rw [hWA,Nat.cast_add]
    have hh:(B.card:ℝ)≤A.card:=by exact_mod_cast geom.index_upper
    linarith
  have hdomain:=ordinary_physical_inner_endpoint_domains Q H A B
  have hS:∀i v,v∈S i→∃w:W,e w=v:=by
    intro i v hv
    exact ⟨⟨v,hdomain.1 i hv⟩,rfl⟩
  have hT:∀i v,v∈T i→∃w:W,e w=v:=by
    intro i v hv
    exact ⟨⟨v,hdomain.2 i hv⟩,rfl⟩
  have hdis:∀i,Disjoint (S i) (T i):=ordinary_boundary_root_domains_disjoint Q H A B
  have hF:∀v,(Fphys.degree v:ℝ)≤εfactor*Fintype.card W:=by
    intro v
    exact (geom.conflict_degree v).trans (hLfactor.trans (mul_le_mul_of_nonneg_left han hεfactor.le))
  have hγcap:2*γ≤endpointCountCoefficient pmin κ:=by
    dsimp [γ]
    have h:=endpointCountCoefficient_pos pmin κ hpmin hκ
    linarith
  have hc:=endpoint_neighborhoods_from_cleanup_inner_scale P Q F H A B π d j s γ κ pmin pR pH density
    tR tH L Ledit βe βh δ εrows σ profile deep geom hrow hindex hLA (le_refl _) hA geom.index_upper hγ.le hγcap hdeg
  have hcounts:∀i,EndpointNeighbourCounts Pinner Fphys (S i) (T i) (γ*Fintype.card W):=by
    intro i
    rw [hW]
    exact hc i
  have hweight:=endpoint_physical_weight_inner_scale P Q F H A B π d j weight κ pmin pR pH L Ledit δ tP η σ
    parent event geom herr
  have hweights:∀i,∃wt:EndpointTriangle Pinner Fphys (S i) (T i)→ℝ,
      (∀C,b/(A.card:ℝ)^2≤wt C ∧ wt C≤Bweight/(A.card:ℝ)^2) ∧
      (∀v∈S i∪T i,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η):=hweight
  exact hN (V⊕U) W {v:V // v∉A} (Sym2 (V⊕U)) e Pinner Fphys S T
    (fun i=>physicalIncidentCoin (Sum.inl i.val)) A.card hnW hJW ha han hsize hS hT hdis hF hcounts hweights
end Oberwolfach
