module

public import Oberwolfach.OrdinaryOriginalMatchingBalanceFamilyPrior
public import Oberwolfach.OrdinaryAssignedVortexExactSamplingData

@[expose] public section
/-! The original selector's weighted matching-and-balance probability is
exactly the prior required by the correction bundle, on the same law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_prior_selector_probability {n qCount K D:ℕ}
    (F:Fin qCount → SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Cres:∀u,Finset (F u).ConnectedComponent) (i₀:Fin K)
    (m d:ℕ) (hd:2 ≤ d) (rsv θ ρ₀ smin lamMatch aRow γrow:ℝ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((m:ℝ)+1) ρ₀ smin d)
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2) → ℝ)
    (seed:(Fin (m+1) → Fin n) → ℝ)
    (t ξ aEvent ζDel lamList bMatch σbal:ℝ)
    {R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e) → Type}
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ)) (E:(Σσ,R σ) → Prop)
    (εE ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ):
    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((m:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((m:ℝ)+1)
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((m:ℝ)+1) D
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p 0 p₂ 0 sampling.u
      sampling.hp (by norm_num) sampling.hp₂ (by norm_num) sampling.hu sampling.hsum d hd q sampling.hq sampling.hQ s sampling.hs sampling.hS)
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((m:ℝ)+1) D (ordinaryEligibleHost P π d) π d w
    let Core:=OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d m p₂ 0 q s wM wO t ξ
    let Match:=OrdinaryRecodedMatchingExtra P π d θ ((m:ℝ)+1) q s aEvent ζDel lamList Core
    let loss:=(((((((εE+3*ζ+χpair)+2*χlist)+χbal)+χbd)+χnbr)+χpairR)+χpath);
    (1-εE ≤ (μ.sigma ρ).probability E → 
      1-loss ≤ (μ.sigma ρ).probability (fun z=>
        ((((E z ∧ Match z.1) ∧
          OrdinaryReferenceBalanceColumnsEvent P (permutationConflictGraph π (3*d)) π d rsv σbal (2*((3*d:ℕ):ℝ)) z.1) ∧
          OrdinaryBoundaryStartEvent π d z.1) ∧ OrdinaryReservedCompletionTests P π d p smin s z.1) ∧
        ∀(Del:SimpleGraph (Fin n)),(∀x,(Del.degree x:ℝ) ≤ bMatch*n) → 
        ∀(Inner:Finset (Fin n)) (tret:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false) tret),
          OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lamMatch aRow γrow m d π P Del Inner z.1 tret Jret)) → 
    1-εE ≤ (μ.sigma ρ).probability E → 
    1-loss ≤ (μ.sigma ρ).probability
      (OrdinaryOriginalMatchingBalanceFamilyPrior P π d m F hF Cres i₀ rsv θ lamMatch aRow γrow
        p smin σbal aEvent ζDel lamList bMatch q s E Core) :=by
  intro p q s p₂ μ wM wO Core Match loss hselector hE
  apply (hselector hE).trans
  apply finiteLaw_probability_mono
  intro z hz
  unfold OrdinaryOriginalMatchingBalanceFamilyPrior
  exact hz
end Oberwolfach
