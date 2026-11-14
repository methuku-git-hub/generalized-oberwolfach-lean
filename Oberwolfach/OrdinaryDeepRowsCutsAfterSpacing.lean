module

public import Oberwolfach.OrdinaryDeepRowsCutsAfterParameters

@[expose] public section
/-! The all-level selector after the spacing and vortex size threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryDeepRowsCutsAfterSpacing
    (m K d:ℕ) (hd:2≤d) (v₀:ℕ) (β:ℝ)
    (α ρ₀ pmin αcut c C a ε₀ ρ θdeep:ℝ)
    (aLoad ε ξ b Bweight ηHub Kdom χinner χdeep eParent hParent εR εH χone χtwo χcut cap:ℝ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∀(θhost p k p₂ k₂ u:ℝ) (hθ:1/2≤θhost) (hthreshold:cycleThreshold (m+1)≤θhost)
      (hdegree:(θhost+α)*Fintype.card V≤D)
      (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    ∀(pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∃weight:∀i,OrdinaryCycle ((P.comap (markedVortexVertexEmbedding Q i)).induce
        ((markedVortexInnerVertices Q i):Set (markedVortexVertexType Q i))) (m+1)→ℝ,
    (∀i,i<Q.length→OrdinaryInnerHubWeightSetupGeneral m (P.comap (markedVortexVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (markedVortexVertexEmbedding Q i))
      (markedVortexInnerVertices Q i) (weight i) pmin (2*p) pH
      (2*pH*(markedVortexInnerHubs Q i).card/(2*p)) β ξ (2*((3*d:ℕ):ℝ)) c C b Bweight ηHub Kdom) ∧
    ∀(density tR tH:ℕ→ℝ) (q:U→Γ→ℝ) (hq:∀w z,0≤q w z) (hQ:∀w,∑z,q w z≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑z,q w z)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let νcoins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)
    let Inner:=OrdinaryUniformInnerHubEvent m P D vsize d β ε Q π hπ (2*p) pH
      (eParent*ε) (hParent*ε) c (4*C/pmin^(3*m+1)) ηHub cap density tR tH s j
    let Deep:=OrdinaryFixedVortexDeepCoverEvent m K d a aLoad ρ θdeep P D vsize β ε Q π hπ j;
    1-loss≤((μ.sigma ν).prod νcoins).probability E→
    1-(loss+χinner+χdeep+χone+χtwo+χcut)≤((μ.sigma ν).prod νcoins).probability
      (fun z=>((((E z ∧ Inner (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        Deep (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ (2*p) pH s j
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D vsize β ε Q π hπ (2*p) pH s j
          (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) ∧
        ∀i,i<Q.length→OrdinaryInducedRimCutEvent (Q.extendedVertices (i+1))
          (sampledOrientation (rawWheelGraph P (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) z.2) αcut pmin)
end Oberwolfach
