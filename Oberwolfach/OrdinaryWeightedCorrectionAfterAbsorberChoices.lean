module

public import Oberwolfach.OrdinaryWeightedCorrectionAfterEarly

@[expose] public section
/-! The correction selector after its conflict, tolerance and absorber
choices; later terminal sizes and probability losses remain arbitrary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryWeightedCorrectionAfterAbsorberChoices
    (r d:ℕ) (hd:2≤d) (mAbs a b:ℕ) (α pstar ω εabs εv L ξ:ℝ):Prop :=
    ∀t f q₀:ℕ,∃N:ℕ,1 ≤ N ∧
    ∀(ζlocal χlocal χglobal χhub χcol C:ℝ),0<ζlocal → 0<χlocal → 0<χglobal → 0<χhub → 0<χcol → 0 ≤ C → 
    ∃Nc Ng Nh Ncol:ℕ,1 ≤ Nc ∧ 1 ≤ Ng ∧ 1 ≤ Nh ∧ 1 ≤ Ncol ∧
    ∀(n qCount K D:ℕ),N ≤ n → Ng ≤ n → ω*n ≤ (qCount:ℝ) → qCount ≤ n → 0<D → 
    ∀(P Bad:SimpleGraph (Fin n)),P.IsRegularOfDegree D → 
      (cycleThreshold r+α)*n ≤ D → (∀v,(Bad.degree v:ℝ) ≤ L) → 
    ∀(π:Equiv.Perm (Fin n)),permutationConflictGraph π (3*d) ≤ Bad → 
      (∀x k,0<k → k<2*d+1 → (π^k) x ≠ x) → 
    ∀(F:Fin qCount → SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (mMatch:ℕ)
      (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1);
    0<ρ₀  →  ρ₀ ≤ initialIndexDensity (Fin qCount) D  →  (1/2:ℝ)*(n:ℝ) ≤ D  → 
    2*pstar ≤ ρ₀*smin  → 
    ∀(A Z Wterm W:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount)),
      A=Finset.univ\Z → (Z.card:ℝ) ≤ εabs*n → 
      Wterm.card+Bterm.card ≤ t → Wterm⊆W → Bterm⊆B → W.card ≤ f → 
      (B.card:ℝ) ≤ εabs*n+f → (Z.card:ℝ) ≤ εv*n → (B.card:ℝ) ≤ εv*n+f → 
      Nc ≤ Z.card → Nh ≤ Z.card → Ncol ≤ Z.card → 0<Htest.card → Htest.card ≤ Z.card → (Htest.card:ℝ) ≤ C*Z.card → 
    ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Type}
      [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ)
      (Cres:∀u,Finset (F u).ConnectedComponent)
      (lamMatch aRow γrow σbal aEvent ζDel lamList bMatch:ℝ)
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2) → ℝ)
      (seed:(Fin (mMatch+1) → Fin n) → ℝ) (tMatch ξMatch:ℝ),
    let E:=fun _:Σσ,R σ=>True
    let εE:ℝ:=0
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let ν:=FiniteLaw.pi (fun _:Sym2 (Fin n)=>FiniteLaw.fairCoin)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ ((mMatch:ℝ)+1) D π d mMatch seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((mMatch:ℝ)+1) D (ordinaryEligibleHost P π d) π d w
    let Core:=OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d mMatch p₂ 0 q s wM wO tMatch ξMatch
    let Match:=OrdinaryRecodedMatchingExtra P π d θ ((mMatch:ℝ)+1) q s aEvent ζDel lamList Core
    let lossE:=(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)
    let Prior:=OrdinaryOriginalMatchingBalanceFamilyPrior P π d mMatch F hF Cres i₀ rsv θ lamMatch aRow γrow
      p smin σbal aEvent ζDel lamList bMatch q s E Core;
    (1-εE ≤ (μ.sigma ρ).probability E → 
      1-lossE ≤ (μ.sigma ρ).probability (fun z=>
        ((((E z ∧ Match z.1) ∧
          OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σbal (2*((3*d:ℕ):ℝ)) z.1) ∧
          OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) ∧
        ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ) ≤ bMatch*n) → 
        ∀(Inner:Finset (Fin n)) (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret),
          OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Inner z.1 tret Jret)) → 
    1-lossE-χcol-χhub-χglobal-2/(n:ℝ)^q₀-(1/(n:ℝ)+2/(n:ℝ)^2)-χlocal ≤ 
      ((μ.sigma ρ).prod ν).probability (fun z=>
      (∀c:Fin 6,∀x∈Z,
        |(((P.neighborFinset x∩Z).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=c)).card:ℝ)-
          markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Z).card|<ζlocal*Z.card) ∧
      ((((Prior z.1 ∧ (∀v∈Z,|rawIntervalUnassignedColumnCount π d (fun e=>z.1.1 (Sum.inr e)) v Htest-
        ∑w∈Htest,(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ))) ∧ (∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1.1 (Sum.inr e)) w Z-
        (Z.card:ℝ)*(1-(∑g,q w g)-(∑j,s w j))|<(Z.card:ℝ)^(3/4:ℝ))) ∧
        OrdinaryZeroRetentionEvent π d false z.1.1) ∧ ∀c x,
        |(sampledColourDegree P (fun e=>(z.1.1 (Sum.inl e)).1) c x:ℝ)-
          markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*P.degree x|<(n:ℝ)^(3/5:ℝ)) ∧
      let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
      OrdinaryCorrectedProtectedReservoir r mAbs t a b ξ (rawWheelGraph P raw\Bad) Bad
        (rawWheelSpokes π d raw false) A Z Wterm Bterm B)
end Oberwolfach
