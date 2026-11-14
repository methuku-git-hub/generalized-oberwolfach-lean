module

public import Oberwolfach.OrdinaryOriginalRegularJointSeedWeightsNormalizedNamed
public import Oberwolfach.OrdinaryClassReserveBound
public import Oberwolfach.CandidateOrdinaryOriginalWeightedRecodedLists
public import Oberwolfach.OrdinaryOriginalRegularJointSeedWeights
public import Oberwolfach.CandidateOrdinaryOriginalCoreRecodedListsDirectReserve

@[expose] public section
/-! The original regular host supplies both seed weights and the matching
core on the assigned sampling law, preserving an arbitrary prior event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalWeightedRecodedListsNormalizedNoFinShape
    (K d m k:ℕ) (hd:2≤d) (hm:7≤m) (hlen:m+1=(k+2)*2)
    (ρ₀ smin θhost α θ:ℝ)
    (hρ₀:0<ρ₀) (hsmin:0<smin)
    (hθhost:1/2≤θhost) (hα:0<α) (hθ:0<θ) (hθ1:θ≤1/100) (hda:1/θ≤d)
    (hspace:1/(4*(d:ℝ))≤5*θ^2/256)
    (hratio:successorCycleRatio k+α/2≤1/2+α):Prop :=
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧
    ∀τ:ℝ,0<τ→∀(t ξ ζ χpair χlist:ℝ),0<t→0<ξ→0<ζ→0<χpair→0<χlist→
    ∃a:ℝ,0<a ∧ ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (hK:0<K) (i₀:Fin K) (rsv c:ℝ) (D:ℕ)
    (hslo:smin≤rsv) (hs1:rsv≤1/100) (hc:8≤c) (hcEq:c=(m:ℝ)+1)
     (hρlo:ρ₀≤ initialIndexDensity U D) (hρ1:initialIndexDensity U D≤1) (hD:0<D)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hthreshold:∀r∈Allowed,cycleThreshold r≤θhost)
    (hClassReserve:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D) (π:Equiv.Perm (Fin n))
    (hdegree:(θhost+α)*(n:ℝ)≤D)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x),
    ∃sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ c ρ₀ smin d,
    ∃w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ,
    ∃seed:(Fin (m+1)→Fin n)→ℝ,
    (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
    (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0) ∧
    (∀i∉longRetainedSeedIndices F hF K θ,∀C,w i C=0) ∧
    SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
      (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed ∧
    ∀(γList βList lamList ζDel:ℝ),0≤γList→0≤βList→0≤lamList→0≤ζDel→
    (∀x,(1/2+γList)*n≤(P.degree x:ℝ))→
    (n:ℝ)^(3/4:ℝ)+2*(2*((3*d:ℕ):ℝ)+1)≤γList*(ρ₀*θ/4)^2*n→
    βList*n+(n:ℝ)^(3/4:ℝ)≤(γList*(ρ₀*θ/4)^2)*n*(θ/2)→
    (lamList+2*ζDel)*n+((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/d≤βList*n→
    ∀{R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity U D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ c D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
    1-εE≤(μ.sigma ν).probability E→
    1-((εE+3*ζ+χpair)+2*χlist)≤(μ.sigma ν).probability (fun z=>E z ∧
      OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ z.1 ∧
      (∀v,((rawIntervalExtendedAnyHubSet π d (fun e=>z.1 (Sum.inr e)) v).card:ℝ)≤
        4*(Fintype.card U:ℝ)/c+4*(n:ℝ)^(3/4:ℝ)) ∧
      (∀w i,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1 (Sum.inr e)) w
          (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i)-
        (rawSelectedNeighbourTestSet P π d (fun e=>z.1 (Sum.inl e)) i).card*(1-(∑g,q w g)-(∑j,s w j))|<(n:ℝ)^(3/4:ℝ)) ∧
      OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1 ∧ OrdinaryProtectedBadEdgeAssignments π d z.1 a ∧
      ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret)
        (Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ)≤ζDel*n)→∀w,
        IsExtendingList (fun x y=>ordinaryPlacementPhysicalRelation P π d (fun e=>z.1 (Sum.inl e)) x y ∧ ¬Del.Adj x y)
          (rawIntervalProtectedUnassignedList π d (fun e=>z.1 (Sum.inr e)) false true tret Jret w) lamList) 
end Oberwolfach
