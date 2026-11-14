module

public import Oberwolfach.OrdinaryFixedVortexAdaptiveHubWeights
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_fixed_vortex_adaptive_hub_weights
    (m d:ℕ) (hm:2≤m) (hd:2≤d)
    (β ε ρ₀ pmin ξ Lconf cLo cHi b Bweight ηHub Kdom χ:ℝ)
    (hβ:0≤β) (hβ1:β≤1/4) (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀)
    (hpmin:0<pmin) (hξ:0<ξ) (hcHi:0<cHi) (hχ:0<χ)
    (hKdom:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom):
    ∃t ζ:ℝ,0<t ∧ 0<ζ ∧ ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ)
      (Dlevel Ledit density tR tH βe βh:ℕ→ℝ)
      (weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ),
      (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH (Dlevel i) β ξ Lconf cLo cHi b Bweight ηHub Kdom)→
      (∀i,i<Q.length→0≤Ledit i ∧ Ledit i≤ζ*(markedVortexInnerVertices Q i).card)→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let J:RawWheelOutcome V U Γ Color→Prop:=fun σ=>∀i,i<Q.length→
      OrdinaryAdaptiveHubWeightsLevelEvent m (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexPermutation Q π hπ i) d
        (2*p) pH (density i) (tR i) (tH i) (Ledit i) (βe i) (βh i) b Bweight ηHub
        (fun z=>s (markedVortexHubEmbedding Q i z)) j
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ);
    1-a≤((μ.sigma ν).prod κ).probability E →
    1-a-χ≤((μ.sigma ν).prod κ).probability (fun z=>E z ∧ J (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨t,ζ,ht,hζ,v₀,hv₀,hraw⟩:=ordinary_fixed_vortex_adaptive_hub_weights m d hm hd
    β ε ρ₀ pmin ξ Lconf cLo cHi b Bweight ηHub Kdom χ hβ hβ1 hε hε1 hρ₀ hpmin hξ hcHi hχ hKdom
  refine ⟨t,ζ,ht,hζ,v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH Dlevel Ledit density tR tH βe βh weight hsetup hedit
    q hq hQ s hs hS j R _ ν κ E a μ J hE
  have hpR:0≤2*p:=by positivity
  have hpR1:2*p≤1:=by linarith
  have hJ:=hraw V U Γ Color P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort
    (2*p) pH hpR hpR1 Dlevel Ledit density tR tH βe βh weight hsetup hedit q hq hQ s hs hS j
  apply ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν κ E J a χ hE
  convert hJ using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
