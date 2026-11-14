module

public import Oberwolfach.OrdinaryMatchingZeroCorrectedGlobalLocalColours
public import Oberwolfach.OrdinaryLocalUnassignedHubsOnPrior
public import Oberwolfach.OrdinaryMatchingCorrectedGlobalLocalColours
public import Oberwolfach.OrdinaryZeroRetentionPrior
public import Oberwolfach.OrdinaryColourDegreesOnPrior
public import Oberwolfach.OrdinaryCorrectedReservoirLocalColoursBeforeSpacing
public import Oberwolfach.OrdinarySameSampleConstructedReservoirBeforeSpacing
public import Oberwolfach.OrdinaryLocalColoursProductPriorUniform
public import Oberwolfach.OrdinarySameSampleReservoirCorrectionEarlyGeometry
public import Oberwolfach.OrdinaryProtectedReservoirHighProbabilityBeforeSpacing
public import Oberwolfach.TwoComponentLower

@[expose] public section
/-! Apply the original uniform absorber probability theorem to construct the
protected reservoir and its correction together with any earlier event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 45000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_matching_corrected_all_local_tests
    (r:ℕ) (hr:3≤r) (α pstar ω:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar≤1) (hω:0<ω):
    ∃δ h εabs εv:ℝ,0<δ ∧ δ<1/4 ∧ 0<h ∧ 0<εabs ∧ 0<εv ∧
    ∀(d:ℕ) (hd:2≤d),∀L:ℝ,0≤L→∀ξ:ℝ,∀hξ:0<ξ,∀hξh:ξ≤h/100,
    ∀m:ℕ,∃a b:ℕ,∀t f q₀:ℕ,∃N:ℕ,1≤N ∧
    ∀(ζlocal χlocal χglobal χhub C:ℝ),0<ζlocal → 0<χlocal → 0<χglobal → 0<χhub → 0≤C → ∃Nc Ng Nh:ℕ,1≤Nc ∧ 1≤Ng ∧ 1≤Nh ∧
    ∀(V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
      N≤Fintype.card V→Ng≤Fintype.card V→ω*Fintype.card V≤(Fintype.card U:ℝ)→Fintype.card U≤Fintype.card V→
    ∀(P F:SimpleGraph V) (D:ℕ),P.IsRegularOfDegree D→0<D→
      (cycleThreshold r+α)*Fintype.card V≤D→(∀v,(F.degree v:ℝ)≤L)→
    ∀(π:Equiv.Perm V),permutationConflictGraph π (3*d)≤F→
      (∀x k,0<k→k<2*d+1→(π^k) x≠x)→
    ∀(p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
      (hsum:2*p+2*k+2*p₂+2*k₂+u≤1) (pH:ℝ),pstar≤2*p→pstar≤pH→pH≤1→
      2*p=initialIndexDensity U D*pH→
    ∀(q:U→Γ→ℝ) (hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (g₀:Γ) (hzero:∀w,q w g₀=0)
      (s:U→Color→ℝ) (hs:∀w j,0≤s w j)
      (hS:∀w,∑j,s w j≤ intervalUncoveredProbability d (∑g,q w g)) (j:Color),(∀w,s w j=pH)→
    ∀(A Z Wterm W:Finset V) (Bterm B Htest:Finset U),
      A=Finset.univ\Z→(Z.card:ℝ)≤εabs*Fintype.card V→
      Wterm.card+Bterm.card≤t→Wterm⊆W→Bterm⊆B→W.card≤f→
      (B.card:ℝ)≤εabs*Fintype.card V+f→
      (Z.card:ℝ)≤εv*Fintype.card V→(B.card:ℝ)≤εv*Fintype.card V+f→Nc≤Z.card→Nh≤Z.card→(Htest.card:ℝ)≤C*Z.card→
    ∀{R:(∀e:RawWheelCoordinate V U,RawExpandedMarkedCoordinateState Γ Color e)→Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
      (E:(Σσ,R σ)→Prop) (lossE:ℝ),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=V) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hS);
    let ν:=FiniteLaw.pi (fun _:Sym2 V=>FiniteLaw.fairCoin);
    1-lossE≤(μ.sigma ρ).probability E→
    1-lossE-χhub-χglobal-2/(Fintype.card V:ℝ)^q₀-(1/(Fintype.card V:ℝ)+2/(Fintype.card V:ℝ)^2)-χlocal≤
      ((μ.sigma ρ).prod ν).probability (fun z=>
      (∀c:Fin 6,∀x∈Z,
        |(((P.neighborFinset x∩Z).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=c)).card:ℝ)-
          markedExpandedPhysicalProbability p k p₂ k₂ u c*(P.neighborFinset x∩Z).card|<ζlocal*Z.card) ∧
      (((E z.1 ∧ (∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1.1 (Sum.inr e)) w Z-
        (Z.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ))) ∧
        OrdinaryZeroRetentionEvent π d g₀ z.1.1) ∧ ∀c x,
        |(sampledColourDegree P (fun e=>(z.1.1 (Sum.inl e)).1) c x:ℝ)-
          markedExpandedPhysicalProbability p k p₂ k₂ u c*P.degree x|<(Fintype.card V:ℝ)^(3/5:ℝ)) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r m t a b ξ (rawWheelGraph P raw\F) F
        (rawWheelSpokes π d raw j) A Z Wterm Bterm B)   :=by
  obtain ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,hbase⟩:=
    ordinary_matching_zero_corrected_global_local_colours r hr α pstar ω hα hpstar hpstar1 hω
  refine ⟨δ,h,εabs,εv,hδ,hδsmall,hh,hεabs,hεv,?_⟩
  intro d hd L hL ξ hξ hξh m
  obtain ⟨a,b,hbase⟩:=hbase d hd L hL ξ hξ hξh m
  refine ⟨a,b,?_⟩
  intro t f q₀
  obtain ⟨N,hN,hbase⟩:=hbase t f q₀
  refine ⟨N,hN,?_⟩
  intro ζlocal χlocal χglobal χhub C hζlocal hχlocal hχglobal hχhub hC
  obtain ⟨Nc,Ng,hNc,hNg,hbase⟩:=hbase ζlocal χlocal χglobal hζlocal hχlocal hχglobal
  obtain ⟨Nh,hNh,hhub⟩:=ordinary_local_unassigned_hubs_on_prior d hd C χhub hC hχhub
  refine ⟨Nc,Ng,Nh,hNc,hNg,hNh,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hng hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ g₀ hzero s hs hS j hj
    A Z Wterm W Bterm B Htest hA hZ hsize hWW hBB hW hB hZsmall hBsmall hZlarge hZhub hHtest R _ ρ E lossE μ ν hE
  let Hub:=fun z:Σσ,R σ=>∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w Z-
    (Z.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ)
  let Prior:=fun z:Σσ,R σ=>E z ∧ Hub z
  have hprior:1-(lossE+χhub)≤(μ.sigma ρ).probability Prior:=
    hhub V U Γ Color Z Htest hZhub hHtest π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hS hnoshort ρ E lossE hE
  have hh:=hbase V U Γ Color hn hng hωn hUn P F D hreg hD hdegree hF π hconf hnoshort
    p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum pH hpR hpH hpH1 hpEq q hq hQ g₀ hzero s hs hS j hj
    A Z Wterm W Bterm B hA hZ hsize hWW hBB hW hB hZsmall hBsmall hZlarge ρ Prior (lossE+χhub) hprior
  dsimp only [Prior,Hub] at hh
  linarith
end Oberwolfach
