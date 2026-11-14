module

public import Oberwolfach.OrdinarySelectedMatchingFamily
public import Oberwolfach.OrdinaryOriginalSelectedMatchingPackages
public import Oberwolfach.OrdinaryMatchingBalanceReservedTests
public import Oberwolfach.OrdinaryZeroRetentionPrior
public import Oberwolfach.CandidateOrdinarySelectedWeightedRecodedListsNormalizedDirectReserve
public import Oberwolfach.CandidateOrdinarySelectedWeightedRecodedListsDirectReserve
public import Oberwolfach.OrdinaryRecodedAbundanceIndependentReserveSelection

@[expose] public section
/-! Choose the seed, recoded-list rates, spacing and abundant reservation in
order, and retain matching, assignments and extending lists on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 65536
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalSameSampleFamilyShape
    (L rstar:ℕ) (βfreq ρ₀ α:ℝ) (hr:3≤rstar) (hβfreq:0<βfreq) (hβ1:βfreq≤1)
    (hρ₀:0<ρ₀) (hα:0<α):Prop :=
    ∃m k:ℕ,L≤m ∧ 7≤m ∧ Even (m+1) ∧ m+1=(k+2)*2 ∧
      successorCycleRatio k+α/2≤1/2+α ∧
    ∀θ:ℝ,0<θ→θ≤1/100→
    ∃βList lamList ζDel smin:ℝ,0<βList ∧ βList≤1 ∧ 0<lamList ∧ 0<ζDel ∧ 0<smin ∧ smin=βfreq/200 ∧
    ∀dNeed:ℕ,∃d K rank:ℕ,dNeed≤d ∧ 2≤d ∧ 3≤K ∧ rstar≤K ∧ 2≤rank ∧ 2*(m+1)≤rank ∧
      (∀i:Fin K,2*(longPaddedSeedExponent i+2)≤rank) ∧
      1/θ≤(d:ℝ) ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧ 1/(2*(K:ℝ))≤βfreq ∧
      5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2 ∧
    ∀(hd' : 2≤d) (θhost:ℝ),1/2≤θhost→
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧
    ∀(lam aRow γ cap:ℝ),0<lam→lam≤1→0<aRow→0<γ→0<cap→
      aRow≤θ/(1600*(K:ℝ)*(K:ℝ))→lam+γ*(1-θ+lam)<θ→
    ∃τ t ξ b:ℝ,0<τ ∧ 0<t ∧ 0<ξ ∧ 0<b ∧ b≤cap ∧ τ≤1/2 ∧ τ≤lam/8 ∧ ξ≤lam/8 ∧ ξ≤1/4 ∧
    ∀(ζ χpair χlist σ χbal χbd χnbr χpairR χpath:ℝ),
      0<ζ→0<χpair→0<χlist→0<σ→0<χbal→0<χbd→0<χnbr→0<χpairR→0<χpath→
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2),
    (∀u,βfreq*n≤((Finset.univ.filter (fun v=>Fintype.card ((F u).connectedComponentMk v)=rstar)).card:ℝ))→
    ∀(D:ℕ),0<D→ρ₀ ≤ initialIndexDensity U D→initialIndexDensity U D≤1→
    ∀(Allowed:Set ℕ), (∀u,AllowedCycleLengths (F u) Allowed)→
      (∀r∈Allowed,cycleThreshold r≤θhost)→
    ∀(P:SimpleGraph (Fin n)),P.IsRegularOfDegree D→
    ∀(π:Equiv.Perm (Fin n)),(θhost+α)*(n:ℝ)≤D→
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    ∃(i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent),
      i₀.val+1=rstar ∧ smin≤rsv ∧ rsv≤1/100 ∧
      (∀u,i₀∈factorShortCandidates (F u) K) ∧
      (∀u c,c∈C u→Fintype.card c=rstar) ∧
      (∀u,(rstar:ℝ)*(C u).card=rsv*n) ∧
      (∀u,rsv≤((Finset.univ.filter (fun v=>longPreparationCycleClass (F u) (hF u) K v=some i₀)).card:ℝ)/n) ∧
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
    (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
    (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
    SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
      (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed ∧
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd' q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D (ordinaryEligibleHost P π d) π d w
    let Core:=OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ
    let Match:=OrdinaryRecodedMatchingExtra P π d θ ((m:ℝ)+1) q s a ζDel lamList Core;
    1-εE≤(μ.sigma ν).probability E→
    1-(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath)≤
      (μ.sigma ν).probability (fun z=>
        ((((E z ∧ Match z.1) ∧
          OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σ (2*((3*d:ℕ):ℝ)) z.1) ∧
          OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) ∧
        ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤b*n)→
        ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret),
          OrdinarySelectedMatchingFamilyResult F hF C i₀ rsv θ lam aRow γ m d π P Del z.1 tret Jret)
end Oberwolfach
