module

public import Oberwolfach.OrdinaryFixedVortexEndpointCommon
public import Oberwolfach.OrdinaryExpandedRawEventProductPrior

@[expose] public section
/-! Fixed endpoint weights and all their potential events can be attached to
any prior on the same expanded sample and direction coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expanded_vortex_endpoint_with_prior
    (β ε ρ₀ α pmin t χ:ℝ) (hβ:0≤β) (hβ1:β≤1/4) (hβα:β≤α/8)
    (hε:0<ε) (hε1:ε<1/4) (hρ₀:0<ρ₀) (hα:0<α) (hpmin:0<pmin) (ht:0<t) (hχ:0<χ)
    (d:ℕ) (hd:2≤d):
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀θhost:ℝ,cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    ∃weight:∀i,markedVortexVertexType Q i→Sym2 (markedVortexVertexType Q i⊕markedVortexHubType Q i)→ℝ,
      (∀i,i<Q.length→EndpointPhysicalParentWeights (P.comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerVertices Q i)ᶜ (weight i)) ∧
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pmin≤2*p→pmin≤pH→
    ∀(q:U→Γ→ℝ) (hq:∀w z,0≤q w z) (hQ:∀w,∑z,q w z≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color),(∀w,s w j=pH)→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κ:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (a:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-a≤((μ.sigma ν).prod κ).probability E→
    1-a-χ≤((μ.sigma ν).prod κ).probability (fun z=>E z ∧
      ∀i,i<Q.length→EndpointPhysicalPotentialEvent
        (P.comap (markedVortexVertexEmbedding Q i))
        ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
        (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
        (markedVortexPermutation Q π hπ i) d j (weight i) (2*p) pH t
        (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i)
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))):=by
  obtain ⟨v₀,hv₀,hcommon⟩:=ordinary_fixed_vortex_endpoint_common β ε ρ₀ α pmin t χ
    hβ hβ1 hβα hε hε1 hρ₀ hα hpmin ht hχ d hd
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort θhost hθ hdegree
  obtain ⟨weight,hweight,hprob⟩:=hcommon V U Γ Color P D vsize hreg hn hD hρlo hρhi hv Q π hπ hnoshort θhost hθ hdegree
  refine ⟨weight,hweight,?_⟩
  intro p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH q hq hQ s hs hS j hj R _ ν κ E a μ hE
  have hp2:0≤2*p:=by positivity
  have hp21:2*p≤1:=by linarith
  let J:RawWheelOutcome V U Γ Color→Prop:=fun σ=>∀i,i<Q.length→EndpointPhysicalPotentialEvent
    (P.comap (markedVortexVertexEmbedding Q i)) ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
    (markedVortexInnerVertices Q i) (markedVortexInnerHubs Q i) (markedVortexInnerVertices Q i)ᶜ
    (markedVortexPermutation Q π hπ i) d j (weight i) (2*p) pH t
    (ordinaryRawRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) σ)
  have hJ:=hprob (2*p) pH hpR hp21 hpH q hq hQ s hs hS j hj
  have hout:=ordinary_expanded_add_raw_event_with_product_prior p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
    ν κ E J a χ hE hJ
  convert hout using 1 <;> congr! 15 <;> exact Subsingleton.elim _ _
end Oberwolfach
