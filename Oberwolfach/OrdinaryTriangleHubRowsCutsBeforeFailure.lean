module

public import Oberwolfach.OrdinaryTriangleFineRowsCutsEvent
public import Oberwolfach.OrdinaryVortexAdaptiveHubAllLevelsEvent
public import Oberwolfach.OrdinaryBufferedHubBeforeFailure

@[expose] public section
/-! Triangle fine cover, both row tests, rim cuts and adaptive hub weights
retain an arbitrary prior on the same sample and reference coins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_triangle_hub_rows_cuts_before_failure
    (α ρ₀ pmin cap:ℝ) (hα:0<α) (hρ₀:0<ρ₀) (hpmin:0<pmin) (hpmin1:pmin≤1) (hcap:0<cap):
    ∃κ c C:ℝ,0<κ ∧ κ≤1 ∧ κ≤cap ∧ 0<c ∧ 0<C ∧
    ∀aLoad:ℝ,0<aLoad→aLoad≤κ→∀ε:ℝ,0<ε→ε<1/4→ε≤κ→ε≤ρ₀/16→
    ∀(d:ℕ) (hd:2≤d) (ξ b Bweight ηHub Kdom ηbal ζlimit:ℝ),
      0<ξ→0<ηbal→0<ζlimit→1+1/(ε/2)+1/((ε/2)*(ρ₀/8))≤Kdom→b≤c→
      (4*C/pmin^(3*2+1))*Kdom^2≤Bweight→
    ∀(buffer:ℕ),2≤buffer→
    ∃t ζ δ δcap rate:ℝ,0<t ∧ 0<ζ ∧ ζ≤ζlimit ∧ 0<δ ∧ δ≤α ∧ 0<δcap ∧ δcap≤ζ/2 ∧ 0<rate ∧
      OrdinaryVortexBufferedTraceCapCostWitness ε ρ₀ α pmin pmin ηbal ζ δ δcap rate d buffer ∧
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
        density tR tH βe βh P Q π hπ s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) :=by
  obtain ⟨κ,hκ,hκ1,hκcap,htri⟩:=ordinary_triangle_fine_rows_cuts_product_prior α ρ₀ pmin cap hα hρ₀ hpmin hpmin1 hcap
  obtain ⟨c,C,hc,hC,hhub⟩:=ordinary_buffered_hub_before_failure 2 (by omega) α hα
  refine ⟨κ,c,C,hκ,hκ1,hκcap,hc,hC,?_⟩
  intro aLoad haLoad haκ ε hε hε1 hεκ hερ d hd ξ b Bweight ηHub Kdom ηbal ζlimit
    hξ hηbal hζlimit hKdom hb hB buffer hbuffer
  obtain ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,hhub⟩:=
    hhub d hd ε ρ₀ pmin ξ b Bweight ηHub Kdom ηbal ζlimit hε hε1 hρ₀ hpmin hpmin1 hξ hηbal hζlimit hKdom hb hB buffer hbuffer
  refine ⟨t,ζ,δ,δcap,rate,ht,hζ,hζlimit',hδ,hδα,hδcap,hδζ,hrate,htrace,?_⟩
  intro εR εH χdeep χHub χone χtwo χcut hεR hεH hχdeep hχHub hχone hχtwo hχcut β hβ hβ1 hβα hβκ hβδ hgap
  obtain ⟨vTri,hvTri,htri⟩:=htri aLoad haLoad haκ ε χdeep hε hε1 hεκ hερ hχdeep β hβ hβ1 hβα hβκ d hd εR εH χone χtwo χcut hεR hεH hχone hχtwo hχcut
  obtain ⟨vHub,hvHub,hhub⟩:=hhub χHub hχHub β hβ hβ1 hβα hβδ hgap
  refine ⟨max vTri vHub,by omega,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P D vsize hreg hn hρlo hρhi hv Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq density tR tH βe βh q hq hQ s hs hS j hj R _ ν E loss μ κcoins αcut Prior hE
  have hprior:1-(loss+χdeep+χone+χtwo+χcut)≤((μ.sigma ν).prod κcoins).probability Prior:=by
    exact htri V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
      p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ s hs hS j hj ν E loss hE
  have hh:=hhub V U Γ Color P D vsize hreg hn hρlo hρhi (by omega) Q π hπ hnoshort θhost hθ hthreshold hdegree
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq density tR tH βe βh
    q hq hQ s hs hS j ν κcoins Prior (loss+χdeep+χone+χtwo+χcut) hprior
  change 1-(loss+χdeep+χone+χtwo+χcut)-χHub≤((μ.sigma ν).prod κcoins).probability (fun z=>
      Prior z ∧ OrdinaryVortexAdaptiveHubAllLevelsEvent 2 d D vsize β ε p pH δcap b Bweight ηHub
        density tR tH βe βh P Q π hπ s j (fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e))) at hh
  linarith only [hh]
end Oberwolfach
