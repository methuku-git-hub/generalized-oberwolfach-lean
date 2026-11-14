module

public import Oberwolfach.OrdinaryCombinedTriangleEvent
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.OrdinaryExpandedGeneralReferenceEvent
public import Oberwolfach.OrdinaryVortexNondeeperDomains

@[expose] public section
/-! Add all fixed nondeeper triangle tests to any dependent event on the
same expanded sample, preserving all five physical state probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nondeeper_triangle_expanded_prior
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P:SimpleGraph V) (D vsize:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε vsize)
    (π:Equiv.Perm V) (πA:∀i,Equiv.Perm (ordinaryVortexNondeeperVertexType Q i))
    (L d k:ℕ) (hd:2≤d) (θ α pstar βP ηP ηH βH c B pH:ℝ)
    (weight:∀i,OrdinaryCycle (P.comap (ordinaryVortexNondeeperVertexEmbedding Q i)) 3→ℝ) (j:Color)
    (p k₁ p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k₁) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k₁+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)→Prop)
    (χ εE:ℝ):
    let A:=fun raw:RawWheelOutcome V U Γ Color=>∀i≤L,ordinaryCombinedTriangleEvent d k
      (P.comap (ordinaryVortexNondeeperVertexEmbedding Q i))
      ((permutationConflictGraph π (3*d)).comap (ordinaryVortexNondeeperVertexEmbedding Q i)) (πA i)
      θ α pstar βP ηP ηH βH c B (2*p) pH (weight i) j
      (ordinaryRawRestrictPair (ordinaryVortexNondeeperVertexEmbedding Q i) (ordinaryVortexNondeeperHubEmbedding Q i) raw);
    1-χ≤(FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith)
      d hd q hq hQ s hs hS)).probability A→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k₁ p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤(μ.sigma ν).probability E→
    1-(εE+χ)≤(μ.sigma ν).probability (fun z=>E z ∧ A (fun e=>expandedOrdinarySelectedCollapse e (z.1 e))) :=by
  intro A hA μ hE
  exact ordinary_expanded_add_general_reference_event p k₁ p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν A E χ εE hA hE
end Oberwolfach
