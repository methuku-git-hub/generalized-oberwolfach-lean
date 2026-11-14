module

public import Oberwolfach.ExpandedReserveBeforeClassProjection
public import Oberwolfach.Definitions
public import Oberwolfach.Neighbourhoods

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance directLongProjectionFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem expanded_long_preparation_projection_direct
    {n q:ℕ} {U Γ Color:Type} [Fintype U] [Fintype Γ] [Fintype Color] [DecidableEq U]
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (d:ℕ) (hd:2≤d) (qHub:U→Γ→ℝ) (hq:∀u g,0≤qHub u g) (hQ:∀u,∑g,qHub u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,qHub u g))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (P:SimpleGraph (Fin n)) (F:Fin q→SimpleGraph (Fin n)) (I:Finset (Fin n)) (ξ:ℝ) (B:ℕ)
    (E:(Σσ,R σ)→Prop):
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd qHub hq hQ s hs hS)
    (∀z,0<(μ.sigma ν).mass z→E z→
      let S₀:=longPhysicalStateGraph P z.1 {0,1,2,3,4};
      ∃A:SimpleGraph (Fin n),A≤S₀ ∧ A.edgeFinset.card≤B ∧
        ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→
          (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
          (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→A≤S→HasFactorDecomposition S F)→
    (μ.sigma ν).probability E≤
      (FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.categorical (expandedBinaryProbability p k p₂ k₂ u)
        (expanded_binary_probability_nonneg p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum)
        (expanded_binary_probability_sum p k p₂ k₂ u))).probability
        (fun γ=>let S₀:=edgeColourGraph P γ 0;
          ∃A:SimpleGraph (Fin n),A≤S₀ ∧ A.edgeFinset.card≤B ∧
            ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→
              (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
              (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→A≤S→HasFactorDecomposition S F) := by
  intro μ hE
  let Btest:=fun γ:Sym2 (Fin n)→Fin 2=>let S₀:=edgeColourGraph P γ 0;
          ∃A:SimpleGraph (Fin n),A≤S₀ ∧ A.edgeFinset.card≤B ∧
            ∀S:SimpleGraph (Fin n),S≤P→S.IsRegularOfDegree (2*q)→
              (∀v,((changed (S₀.neighborFinset v) (S.neighborFinset v)).card:ℝ)≤ξ*n)→
              (∀x∈I,∀y∈I,S.Adj x y↔S₀.Adj x y)→A≤S→HasFactorDecomposition S F
  apply le_trans ?_ (le_of_eq (expanded_binary_colour_probability_after_retention p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd qHub hq hQ s hs hS ν Btest))
  apply finiteLaw_probability_mono_on_support (μ.sigma ν) E _
  intro z hz he
  dsimp only [Btest]
  rw [expanded_binary_class_graph P z.1]
  have hdec:directLongProjectionFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  have hdec6:directLongProjectionFin 6=instDecidableEqFin 6:=Subsingleton.elim _ _
  try rw [hdec6] at hE
  try rw [hdec6]
  try rw [hdec] at hE
  try rw [hdec]
  obtain ⟨A,hA,hcard,hall⟩:=hE z hz he
  refine ⟨A,hA,?_,?_⟩
  · simpa using hcard
  · intro S hSP hreg hedit hagree hAS
    apply hall S hSP hreg
    · simpa using hedit
    · exact hagree
    · exact hAS
end Oberwolfach
