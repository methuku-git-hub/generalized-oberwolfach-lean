module

public import Oberwolfach.OrdinaryFixedVortexTriangleSeparatedCover
public import Oberwolfach.OrdinaryExpandedRawAndCoinEvents

@[expose] public section
/-! Add the separated cover event to an arbitrary existing expanded-sample
and direction-coin event, preserving the original physical raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_fixed_vortex_triangle_separated_expanded
    (α ρ₀ p:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hp:0<p) (hp1:p≤1):
    ∃a₀ ε₀ ρhub η θ ρ:ℝ,0<a₀ ∧ 0<ε₀ ∧ 0<ρhub ∧ 0<η ∧ 0<θ ∧ 0<ρ ∧
    ∀(ε χ:ℝ),0<ε→ε<1/4→ε≤ρ₀/16→0<χ→
    ∀a:ℝ,0<a→a≤a₀→∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤ε₀→
    ∀d:ℕ,∀hd:2≤d,∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→
      (θhost+α)*Fintype.card V≤D→
    ∀(pR pH:ℝ) (hpR:p≤pR) (hpR1:pR≤1),p≤pH→pH≤1→pR=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀u z,0≤q u z) (hQ:∀u,∑z,q u z≤1/8)
      (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
      (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑z,q u z)) (j:Color) (hj:∀u,s u j=pH),
    ∀(pp k p₂ k₂ u:ℝ) (hp₀:0≤pp) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*pp+2*k+2*p₂+2*k₂+u≤1),pR=2*pp→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) pp k p₂ k₂ u hp₀ hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let coins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-εE≤((μ.sigma ν).prod coins).probability E→
    1-(εE+χ)≤((μ.sigma ν).prod coins).probability (fun z=> E z ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      ∀i,i<Q.length→
        let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
        let ρi:=markedVortexPermutation Q π hπ i;let J:=markedVortexInnerHubs Q i;
        let raw:=ordinaryRawRestrictPair f g raw;
        OrdinaryPrescribedInnerEvent 3 (P.comap f) ((permutationConflictGraph π (3*d)).comap f) ρi d a p (min (α/2) 1)
          Finset.univ Finset.univ j raw ∧
        OrdinaryHubCoverEvent 2 (P.comap f) ((permutationConflictGraph π (3*d)).comap f) ρi d ρhub j raw ∧
        OrdinaryTriangleTwoDomainRowEvent (P.comap f) ((permutationConflictGraph π (3*d)).comap f) ρi d (2*(3*d))
          Finset.univ Finset.univ (Finset.univ\J) pR pH η θ ρ j raw) :=by
  obtain ⟨a₀,ε₀,ρhub,η,θ,ρ,ha₀,hε₀,hρhub,hη,hθ,hρ,hbase⟩:=
    ordinary_fixed_vortex_triangle_separated_cover α ρ₀ p hα hρ₀ hp hp1
  refine ⟨a₀,ε₀,ρhub,η,θ,ρ,ha₀,hε₀,hρhub,hη,hθ,hρ,?_⟩
  intro ε χ hε hε1 hεsmall hχ a ha ha₀ β hβ hβ1 hβα hβε d hd
  obtain ⟨v₀,hv₀,hbase⟩:=hbase ε χ hε hε1 hεsmall hχ a ha ha₀ β hβ hβ1 hβα hβε d hd
  refine ⟨v₀,hv₀,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    pR pH hpR hpR1 hpH hpH1 hpEq q hq hQ s hs hS j hj pp k p₂ k₂ u hp₀ hk hp₂ hk₂ hu hsum hpR_eq
    R _ ν E εE μ coins hE
  have hA:=hbase V U Γ Color P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    pR pH hpR hpR1 hpH hpH1 hpEq q hq hQ s hs hS j hj
  clear hpEq
  subst pR
  let μrc := (FiniteLaw.pi (rawWheelLaw (V:=V) (fun _=>2*pp)
      (fun _=>by linarith) (fun _=>by linarith) d hd q hq hQ s hs hS)).prod coins
  have htrivial:1-(0:ℝ)≤μrc.probability (fun _=>True) :=by
    simp [FiniteLaw.probability, μrc.total]
  have hout:=ordinary_expanded_add_raw_and_coin_events pp k p₂ k₂ u hp₀ hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS ν E
    (fun σ=> ∀i,i<Q.length→
        let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
        let ρi:=markedVortexPermutation Q π hπ i;let J:=markedVortexInnerHubs Q i;
        let raw:=ordinaryRawRestrictPair f g σ;
        OrdinaryPrescribedInnerEvent 3 (P.comap f) ((permutationConflictGraph π (3*d)).comap f) ρi d a p (min (α/2) 1)
          Finset.univ Finset.univ j raw ∧
        OrdinaryHubCoverEvent 2 (P.comap f) ((permutationConflictGraph π (3*d)).comap f) ρi d ρhub j raw ∧
        OrdinaryTriangleTwoDomainRowEvent (P.comap f) ((permutationConflictGraph π (3*d)).comap f) ρi d (2*(3*d))
          Finset.univ Finset.univ (Finset.univ\J) (2*pp) pH η θ ρ j raw) (fun _=>True) εE χ 0 hA htrivial hE
  simpa using hout
end Oberwolfach
