module

public import Oberwolfach.OrdinaryTriangleReferenceJoint
public import Oberwolfach.OrdinaryRawPairRestriction
public import Oberwolfach.OrdinaryVortexNondeeperDomains
public import Oberwolfach.FiniteProjectedProductEvent
public import Oberwolfach.ExpandedOrdinarySelectedLaw
public import Oberwolfach.FiniteSigmaFirstMap

@[expose] public section
/-! Attach all nondeeper reference cuts to an arbitrary event of the same
expanded sample and direction coins, including the reservoir event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_nondeeper_cuts_expanded_prior
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [DecidableEq U]
    (P F:SimpleGraph V) (D vsize:ℕ) (β ε:ℝ) (Q:Vortex U P D β ε vsize)
    (πA:∀i,Equiv.Perm (ordinaryVortexNondeeperVertexType Q i)) (L d:ℕ) (hd:2≤d) (j:Color) (δ h:ℝ)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
    (s:U→Color→ℝ) (hs:∀w j,0≤s w j) (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (εE χ:ℝ):
    let A:=fun z:RawWheelOutcome V U Γ Color×(Sym2 V→Bool)=>∀i≤L,
      OrdinaryTriangleReferenceNormalizedCuts (P.comap (ordinaryVortexNondeeperVertexEmbedding Q i))
        (F.comap (ordinaryVortexNondeeperVertexEmbedding Q i)) (πA i) d j δ h
        (ordinaryRawRestrictPair (ordinaryVortexNondeeperVertexEmbedding Q i) (ordinaryVortexNondeeperHubEmbedding Q i) z.1)
        (fun e=>z.2 (Sym2.map (ordinaryVortexNondeeperVertexEmbedding Q i) e));
    let μraw:=FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*p) (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-χ≤(μraw.prod ν).probability A→
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤((μ.sigma ρ).prod ν).probability E→
    1-εE-χ≤((μ.sigma ρ).prod ν).probability (fun z=>E z∧
      A (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e),z.2)) :=by
  intro A μraw ν hA μ hE
  let f:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→RawWheelOutcome V U Γ Color:=
    fun σ e=>expandedOrdinarySelectedCollapse e (σ e)
  have hproj:(μ.sigma ρ).map (fun z=>f z.1)=μraw:=by
    calc
      _ = ((μ.sigma ρ).map Sigma.fst).map f:=by rw [finiteLaw_map_map]
      _ = μ.map f:=by rw [finiteLaw_sigma_map_first_dependent]
      _ = μraw:=expanded_ordinary_selected_wheel_law p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS
  exact finite_projected_product_event (μ.sigma ρ) μraw ν (fun z=>f z.1) hproj E A εE χ hE hA
end Oberwolfach
