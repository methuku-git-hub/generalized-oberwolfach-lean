module

public import Oberwolfach.OrdinaryNamedTriangleInnerEndpointBeforeFailure
public import Oberwolfach.OrdinaryTriangleRootFreeNumericFixedMargin

@[expose] public section
/-! Choose one host submargin before the inner-hub constants, then use those
same constants in the triangle inner-certificate hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryNamedTriangleInnerEndpointSelectorRootFree (α c C:ℝ):Prop :=
    ∀(ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent:ℝ),
      0<ε  →  ε<1/4  →  0<ρ₀  →  0<pmin  →  pmin ≤ 1  →  0<ξ  → 
      2/ε ≤ Kdom  →  1+1/(ε/2)+1/((ε/2)*(ρ₀/8)) ≤ Kdom  → 
      b ≤ c  →  (4*C/pmin^(7))*Kdom^2 ≤ Bweight  →  0<eParent  →  0<hParent  → 
    ∃t eEvent hEvent cap:ℝ,0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent ≤ eParent ∧ hEvent ≤ hParent ∧
    ∀χ:ℝ,0<χ→∀(d:ℕ) (hd:2≤d),∀β:ℝ,0 ≤ β  →  β ≤ 1/4  →  β ≤ α/8  →  ξ+2*β<ηHub  →  ∀(tpot χend:ℝ),0<tpot→0<χend→∃v₀:ℕ,1 ≤ v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D  →  0<Fintype.card V  → 
      ρ₀ ≤ initialIndexDensity U D  →  initialIndexDensity U D ≤ 1  →  v₀ ≤ vsize  → 
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l  →  l<2*d+1  →  (π^l) x≠x)  → 
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2 ≤ θhost) (hthreshold:cycleThreshold 3 ≤ θhost)
      (hdegree:(θhost+α)*Fintype.card V ≤ D)
      (hp:0 ≤ p) (hk:0 ≤ k) (hp₂:0 ≤ p₂) (hk₂:0 ≤ k₂) (hu:0 ≤ u) (hsum:2*p+2*k+2*p₂+2*k₂+u ≤ 1),
    ∀(pH:ℝ),pmin ≤ 2*p  →  2*p ≤ 1  →  pmin ≤ pH  →  pH ≤ 1  →  2*p=initialIndexDensity U D*pH  → 
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) 3 → ℝ,
    (∀i,i<Q.length  →  OrdinaryInnerHubWeightSetupGeneral 2 (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    ∃endpointWeight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
    (∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (endpointWeight i)) ∧
    ∀(density tR tH:ℕ → ℝ) (q:U → Γ → ℝ) (hq:∀u z,0 ≤ q u z) (hQ:∀u,∑z,q u z ≤ 1/8)
      (s:U → Color → ℝ) (hs:∀u j,0 ≤ s u j)
      (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    (∀u,s u j=pH)→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e) → Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V → Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V → Bool) → Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let J:=OrdinaryUniformInnerHubEvent 2 P D vsize d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(7)) ηHub cap density tR tH s j;
    1-a ≤ ((μ.sigma ν).prod κ).probability E  → 
    1-a-χ-χend ≤ ((μ.sigma ν).prod κ).probability (fun z=>(E z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
      ∀i,i<Q.length→EndpointPhysicalPotentialEvent
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (endpointWeight i) (2*p) pH tpot
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))))

def OrdinaryTriangleRootFreeSharpNumericAtMargin (pmin κe bHub BHub α ρ₀ pstar ηP:ℝ) (hpstar:0<pstar):Prop :=
    ∃δ href βP:ℝ,0<δ ∧ δ<1/8 ∧ 0<href ∧ 0<βP ∧
    ∃k:ℕ,∃βH cParent Bparent:ℝ,5≤k ∧ 0<βH ∧ 0<cParent ∧ 0<Bparent ∧
    (∀(d:ℕ) (hd:2≤d),∀ηH η χhost χcut:ℝ,0<ηH→0<η→η<1→0<χhost→0<χcut→
      ∃εTri:ℝ,0<εTri ∧ ∃Mhost Mcut:ℕ,1≤Mhost ∧ 1≤Mcut ∧
      OrdinaryTriangleFixedDomainSelector k d Mhost hd (max (1/2) (cycleThreshold 3)) (α/2) pstar
        (ρ₀/16) βP ηP ηH βH cParent Bparent εTri η χhost (2*(3*d)) hpstar ∧
      OrdinaryReferenceCutsDomainSelector d Mcut hd (α/2) pstar (ρ₀/16) (2*δ) href η χcut (2*(3*d))) ∧
    ∃εstar cLinear εf ηhub ηend ζfresh εrows:ℝ,0<εstar ∧ 0<cLinear ∧ 0<εf ∧ 0<ηhub ∧ 0<ηend ∧ 0<ζfresh ∧ 0<εrows ∧
    ∃δInner εcount tpot lamInner:ℝ,
      OrdinaryTriangleInnerNumericParameters pmin κe εf ηend εrows δInner εcount tpot lamInner ∧
      OrdinaryTriangleRootFreeSharpInnerAfterChoice (α/2) k (ρ₀/16) (βH/8) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (href/4) δ εstar cLinear κe pmin bHub BHub εf ηhub ηend ζfresh εrows ∧
    ∀ηHcap gapcap ζcap:ℝ,0<ηHcap→0<gapcap→0<ζcap→ζcap≤href→
    ∃ηH gap:ℝ,0<ηH ∧ ηH≤ηHcap ∧ 0<gap ∧ gap≤gapcap ∧ 2*ηH+gap<εstar ∧
    ∃ζroot rateRoot lamRoot:ℝ,0<ζroot ∧ 0<rateRoot ∧ 0<lamRoot ∧ ζroot≤ζcap ∧
    ∃N₀:ℕ,1≤N₀ ∧
      OrdinaryTriangleEditScaleAt βH ηH Bparent (ρ₀/16) pstar (βH/2) (2*ηH) ζroot rateRoot N₀ ∧
      OrdinaryUniformRootReferenceAtScale 3 (by omega) k (α/2) (βH/2) cParent (Bparent/((ρ₀/16)*pstar^(2*3-1)))
        (2*href-ζroot) (2*δ) (2*ηH) (ρ₀/16) gap lamRoot ∧
    ∃ξGeo ζGeo edit:ℝ,0<ξGeo ∧ 0<ζGeo ∧ 0<edit ∧ ξGeo≤href/4 ∧ ζGeo≤href/4 ∧ ξGeo+ζGeo≤href/2 ∧
      href/4≤(2*href-ζroot)-ξGeo-ζGeo ∧
    ∀pcap:ℝ,0<pcap→∃p:ℝ,0<p ∧ p≤1 ∧ p≤pcap ∧
    ∀η:ℝ,0<η→∃eps γgeo:ℝ,0<eps ∧ eps≤1 ∧ 0<γgeo ∧
      OrdinaryVortexBufferedRootStaticGeometrySeparateAtScale 3 k 2 ρ₀ (βH/4) (cParent*(1-2*δ)^2)
        (Bparent/((ρ₀/16)*pstar^(2*3-1))) (2*ηH+gap) (εstar-(2*ηH+gap))
        (βH/8) ξGeo ζGeo edit p η eps γgeo

theorem ordinary_triangle_original_root_free_inner_endpoint_hierarchy
    (θ α₀ ρ₀ pstar ηP pmin κe:ℝ)
    (hθhalf:1/2≤θ) (hθcycle:cycleThreshold 3≤θ) (hθ1:θ<1) (hα₀:0<α₀)
    (hρ₀:0<ρ₀) (hpstar:0<pstar) (hpstar1:pstar≤1) (hηP:0<ηP)
    (hpmin:0<pmin) (hpmin1:pmin≤1) (hκe:0<κe):
    ∃α c C:ℝ,0<α ∧ α≤α₀ ∧ α≤1 ∧ max (1/2) (cycleThreshold 3)+α/4≤1 ∧
      0<c ∧ 0<C ∧ OrdinaryNamedTriangleInnerEndpointSelectorRootFree (α/2) c C ∧
      OrdinaryTriangleRootFreeSharpNumericAtMargin pmin κe c (4*C/pmin^7) α ρ₀ pstar ηP hpstar :=by
  obtain ⟨α,hα,hαsub,hα1,hmargin⟩:=ordinary_triangle_reference_submargin θ α₀ hθhalf hθcycle hθ1 hα₀
  obtain ⟨c,C,hc,hC,hselect⟩:=ordinary_named_triangle_inner_endpoint_before_failure (α/2) (by positivity)
  have hnum:=ordinary_triangle_root_free_sharp_numeric_fixed_margin pmin κe c (4*C/pmin^7) α ρ₀ pstar ηP
    hpmin hpmin1 hκe hc (by positivity) hα hα1 hmargin hρ₀ hpstar hpstar1 hηP
  exact ⟨α,c,C,hα,hαsub,hα1,hmargin,hc,hC,hselect,hnum⟩
end Oberwolfach
