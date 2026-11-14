module

public import Oberwolfach.OrdinaryTriangleHubRowsCutsBeforeFailure

@[expose] public section
/-! The triangle event selector after its trace and edit caps are fixed,
before choosing any failure allowances. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryTriangleHubAfterCapBeforeFailure
    (d:ℕ) (hd:2≤d) (α ρ₀ pmin κ aLoad ε ξ b Bweight ηHub δ δcap:ℝ):Prop :=
    ∀(εR εH χdeep χHub χone χtwo χcut:ℝ),0<εR→0<εH→0<χdeep→0<χHub→0<χone→0<χtwo→0<χcut→
    ∀β:ℝ,0≤β→β≤1/4→β≤α/8→β≤κ→β≤δ→ξ+2*β<ηHub→
    ∃v₀:ℕ,1≤v₀ ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [LinearOrder U],
    ∀(P:SimpleGraph V) (D vsize:ℕ),P.IsRegularOfDegree D→0<Fintype.card V→
      ρ₀≤ initialIndexDensity U D→initialIndexDensity U D≤1→v₀≤vsize→
    ∀(Q:Vortex U P D β ε vsize) (π:Equiv.Perm V)
      (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(θhost:ℝ),1/2≤θhost→cycleThreshold 3≤θhost→(θhost+α)*Fintype.card V≤D→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pmin≤2*p→pmin≤pH→pH≤1→2*p=initialIndexDensity U D*pH→
    ∀(density tR tH βe βh:ℕ→ℝ)
      (q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color) (hj:∀w,s w j=pH),
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)×(Sym2 V→Bool)→Prop) (loss:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS)
    let κcoins:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin)
    let αcut:=min (α/4) (1/4:ℝ)
    let Prior:=OrdinaryTriangleFineRowsCutsEvent d κ aLoad εR εH αcut pmin p pH P D vsize β ε Q π hπ s j E;
    1-loss≤((μ.sigma ν).prod κcoins).probability E→
    1-(loss+χdeep+χone+χtwo+χcut+χHub)≤((μ.sigma ν).prod κcoins).probability (fun z=>
      Prior z ∧ OrdinaryVortexAdaptiveHubAllLevelsEvent 2 d D vsize β ε p pH δcap b Bweight ηHub
        density tR tH βe βh P Q π hπ s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e)))
end Oberwolfach
