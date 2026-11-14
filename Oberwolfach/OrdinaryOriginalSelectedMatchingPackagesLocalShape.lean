module

public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData
public import Oberwolfach.OrdinarySelectedMatchingPackagesLocalResult
public import Oberwolfach.OrdinaryOriginalSelectedMatchingInputs
public import Oberwolfach.OrdinaryMatchingEventErrorInputs
public import Oberwolfach.OrdinaryMatchingWeightConstants

@[expose] public section
/-! Original-host, selected-weight and same-sample input shape for the
physical matching packages, with matching tolerances chosen before the graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

def OrdinaryOriginalSelectedMatchingPackagesLocalShape
    (r K m k d:ℕ) (hr:2≤r) (hK3:3≤K) (hm:7≤m) (hd:2≤d)
    (hrM:2*(m+1)≤r) (hrO:∀i:Fin K,2*(longPaddedSeedExponent i+2)≤r)
    (θ a γ αHost ρ₀ lam cap:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (ha:0<a) (hγ:0<γ)
    (hα:0<αHost) (hρ₀:0<ρ₀) (hlam:0<lam) (hlam1:lam≤1) (hcap:0<cap)
    (haBound:a≤θ/(1600*(K:ℝ)*(K:ℝ))) (hda:1/θ≤d)
    (hslack:lam+γ*(1-θ+lam)<θ)
    (hcutHost:5/(((m:ℝ)+1)*(d:ℝ)+5)+((m:ℝ)+1)*(d:ℝ)/(K:ℝ)≤θ/2)
    (B:Fin K→ℝ) (hB:∀i,0<B i):Prop :=
    ∃τ t ξ b:ℝ,0<τ ∧ 0<t ∧ 0<ξ ∧ 0<b ∧ b≤cap ∧
      τ≤1/2 ∧ τ≤lam/8 ∧ ξ≤lam/8 ∧ ξ≤1/4 ∧
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U],Fintype.card U≤n→
    ∀(F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (i₀:Fin K) (rsv smin:ℝ) (hsmin:0<smin) (hslo:smin≤rsv) (hs1:rsv≤1/100)
    (hClass:OrdinaryClassReserveBound F hF i₀ rsv)
    (P:SimpleGraph (Fin n)) (D:ℕ) (hreg:P.IsRegularOfDegree D) (hD:0<D)
    (θhost:ℝ) (hhost:1/2≤θhost) (hdegree:(θhost+αHost)*(n:ℝ)≤D)
    (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
    (π:Equiv.Perm (Fin n)) (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (hw:∀i C,0≤w i C ∧ w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i))
    (he:∀i∈longRetainedSeedIndices F hF K θ,∀x y,
      (∑C,if C.val.val.Adj x y then w i C else 0)=if (ordinaryEligibleHost P π d).Adj x y then 1 else 0)
    (seed:(Fin (m+1)→Fin n)→ℝ)
    (hseed:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
      (successorWeightLower k (αHost/4)) (successorWeightUpper k (αHost/4)) seed)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (hCres:∀u c,c∈Cres u→Fintype.card c=i₀.val+1)
    (hres:∀u,((i₀.val+1:ℕ):ℝ)*(Cres u).card=rsv*n)
    (Del:SimpleGraph (Fin n)) (hDel:∀x,(Del.degree x:ℝ)≤b*n) (Inner:Finset (Fin n))
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e),
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D (ordinaryEligibleHost P π d) π d w;
    OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ σ→
    ∀(tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) tret),
      OrdinarySelectedMatchingPackagesLocalResult F hF Cres i₀ rsv θ lam a γ m d π P Del Inner σ tret Jret
end Oberwolfach
