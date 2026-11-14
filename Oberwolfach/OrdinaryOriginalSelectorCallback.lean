module

public import Oberwolfach.OrdinaryOriginalSelectorFactorWitness

@[expose] public section
/-! The original selector's callback after fixing its matching witnesses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryOriginalSelectorCallback
    (n qCount D rstar m k d K:ℕ) (hd:2≤d)
    (ρ₀ θ lam aRow γ lamList ζDel smin τ t ξ b σ ζ χpair χlist χbal χbd χnbr χpairR χpath a α:ℝ)
    (BO:Fin K→ℝ) (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (i₀:Fin K) (rsv:ℝ) (C:∀u,Finset (F u).ConnectedComponent)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (m+1)→Fin n)→ℝ):Prop :=
    ∀{R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ))
    (E:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)→Prop) (εE:ℝ),
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
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
        ∀(Inner:Finset (Fin n)) (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret),
          OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF C i₀ rsv θ lam aRow γ m d π P Del Inner z.1 tret Jret)
end Oberwolfach
