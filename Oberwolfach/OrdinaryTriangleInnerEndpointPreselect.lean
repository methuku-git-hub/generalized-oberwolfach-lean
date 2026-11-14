module

public import Oberwolfach.OrdinaryTriangleOriginalInnerEndpointHierarchy

@[expose] public section
/-! Fix the inner-hub selector's cap before failure allowance and conflict
spacing, using constants from the same earlier triangle hierarchy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleInnerEndpointAfterSetup
    (α c C ε ρ₀ pmin ξ b Bweight ηHub Kdom eParent hParent cap:ℝ):Prop :=
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

theorem ordinary_triangle_inner_endpoint_preselect
    (α c C ε ρ₀ pmin ηHub eParent hParent:ℝ)
    (hselector:OrdinaryNamedTriangleInnerEndpointSelector α c C)
    (hc:0<c) (hC:0<C) (hε:0<ε) (hε1:ε<1/4) (hρ:0<ρ₀)
    (hp:0<pmin) (hp1:pmin≤1) (hη:0<ηHub) (he:0<eParent) (hh:0<hParent):
    ∃ξ Kdom Bweight t eEvent hEvent cap:ℝ,
      0<ξ ∧ ξ<ηHub ∧ 0<Kdom ∧ 0<Bweight ∧ 0<t ∧ 0<eEvent ∧ 0<hEvent ∧ 0<cap ∧
      eEvent≤eParent ∧ hEvent≤hParent ∧
      OrdinaryTriangleInnerEndpointAfterSetup α c C ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent cap :=by
  let ξ:=ηHub/4
  let Kdom:=1+1/(ε/2)+1/((ε/2)*(ρ₀/8))+2/ε
  let Bweight:ℝ:=(4*C/pmin^7)*Kdom^2
  have hξ:0<ξ:=by dsimp [ξ];positivity
  have hξcap:ξ<ηHub:=by dsimp [ξ];linarith
  have hK:0<Kdom:=by dsimp [Kdom];positivity
  have hB:0<Bweight:=by dsimp [Bweight];positivity
  have hA:0≤1/(ε/2):=by positivity
  have hB':0≤1/((ε/2)*(ρ₀/8)):=by positivity
  have hC':0≤2/ε:=by positivity
  have hK1:2/ε≤Kdom:=by dsimp [Kdom];linarith
  have hK2:1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom:=by dsimp [Kdom];linarith
  obtain ⟨t,eEvent,hEvent,cap,ht,hevent,hhevent,hcap,hebound,hhbound,hafter⟩:=
    hselector ε ρ₀ pmin ξ c Bweight ηHub Kdom eParent hParent hε hε1 hρ hp hp1 hξ hK1 hK2
      (le_refl _) (by dsimp [Bweight];exact le_rfl) he hh
  exact ⟨ξ,Kdom,Bweight,t,eEvent,hEvent,cap,hξ,hξcap,hK,hB,ht,hevent,hhevent,hcap,hebound,hhbound,hafter⟩
end Oberwolfach
