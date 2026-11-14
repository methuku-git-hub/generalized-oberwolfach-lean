module

public import Oberwolfach.OrdinaryNamedInnerHubBeforeFailure
public import Oberwolfach.OrdinaryExpandedVortexEndpointAttachedPrior

@[expose] public section
/-! Select inner hub and endpoint weights before sampling and attach their
two events to an arbitrary prior on one expanded sample and coin outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_named_triangle_inner_endpoint_before_failure
    (α:ℝ) (hα:0<α):
    ∃c C:ℝ,0<c ∧ 0<C ∧
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
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))) :=by
  obtain ⟨c,C,hc,hC,hinner⟩:=ordinary_named_inner_hub_before_failure 2 (by omega) α hα
  refine ⟨c,C,hc,hC,?_⟩
  intro ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent hε hε1 hρ₀ hpmin hpmin1 hξ
    hK hKdom hb hB he hh
  obtain ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,hinner⟩:=
    hinner ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent hε hε1 hρ₀ hpmin hpmin1 hξ
      hK hKdom hb hB he hh
  refine ⟨t,eEvent,hEvent,cap,ht,heEvent,hhEvent,hcap,heBound,hhBound,?_⟩
  intro χ hχ d hd β hβ hβ1 hβα hgap tpot χend htpot hχend
  obtain ⟨vInner,hvInner,hinner⟩:=hinner χ hχ d hd β hβ hβ1 hβα hgap
  obtain ⟨vEnd,hvEnd,hend⟩:=ordinary_expanded_vortex_endpoint_with_attached_prior β ε ρ₀ α pmin tpot χend
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin htpot hχend d hd
  refine ⟨max vInner vEnd,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpR1 hpH hpH1 hpEq
  have hD:(Fintype.card V:ℝ)/2 ≤ D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=by positivity
    nlinarith [mul_nonneg hα.le hn0,mul_nonneg (show 0≤θhost-1/2 by linarith) hn0]
  obtain ⟨weight,hweight,hinner⟩:=hinner V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort
    θhost p k p₂ k₂ u hθ hthreshold hdegree hp hk hp₂ hk₂ hu hsum pH hpR hpR1 hpH hpH1 hpEq
  obtain ⟨endpointWeight,hweightEnd,hend⟩:=hend V U Γ Color P D vsize hreg hn hD hρlo hρhi (by omega) Q π hπ hnoshort
    θhost hthreshold hdegree
  refine ⟨weight,hweight,endpointWeight,hweightEnd,?_⟩
  intro density tR tH q hq hQ s hs hS j hj R _ ν κ E a μ J hE
  have hi:=hinner density tR tH q hq hQ s hs hS j ν κ E a hE
  have hout:=hend p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH q hq hQ s hs hS j hj ν κ E J (a+χ) (by linarith)
  convert hout using 1 <;> try linarith <;> congr! 15 <;> exact Subsingleton.elim _ _
end Oberwolfach
