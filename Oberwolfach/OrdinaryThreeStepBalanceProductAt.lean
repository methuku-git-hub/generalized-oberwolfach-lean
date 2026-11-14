module

public import Oberwolfach.OrdinaryExpandedThreeStepBalanceProductPrior

@[expose] public section
/-! A fixed threshold for attaching three-step balance to any product
prior on the selected expanded sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryThreeStepBalanceProductAt
    (d:ℕ) (hd:2≤d) (εR εH β ε ρ₀ χ:ℝ) (m₀:ℕ):Prop :=
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀(P F:SimpleGraph V) (D m:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      (Fintype.card V:ℝ)/2≤D→ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→m₀≤m→
    ∀(Q:VortexLookback U P D β ε m 2) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→permutationConflictGraph π (3*d)≤F→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (pH:ℝ) (hj:∀w,s w j=pH) (hpH:0≤pH)
      (hbalance:2*p=initialIndexDensity U D*pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)) (κcoins:FiniteLaw (Sym2 V→Bool))
      (E:(Σσ:∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e,R σ)×(Sym2 V→Bool)→Prop) (εE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    1-εE≤((μ.sigma ν).prod κcoins).probability E→
    1-(εE+χ)≤((μ.sigma ν).prod κcoins).probability (fun z=>E z ∧
      OrdinaryVortexThreeStepRowIndexEvent 3 d εR εH P F D m β ε Q.toVortex π hπ (2*p) pH s j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)) ∧
      OrdinaryVortexThreeStepEditedBalanceEvent P D m β ε pH εR εH Q π hπ d j
        (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))
end Oberwolfach
