module

public import Oberwolfach.OrdinaryAssignedCorrectionEvent

@[expose] public section
/-! The earlier bound is the probability of the named event on the same law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_correction_named_probability
    (r d mAbs a b t q₀ n qCount K D:ℕ) (hd:2≤d)
    (ζlocal χlocal χglobal χhub χcol ξ:ℝ)
    (P Bad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:Fin qCount→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (mMatch:ℕ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d)
    (A Z Wterm:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount))
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (lamMatch aRow γrow σbal aEvent ζDel lamList bMatch:ℝ)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
    (seed:(Fin (mMatch+1)→Fin n)→ℝ) (tMatch ξMatch:ℝ)    (h:OrdinaryAssignedCorrectionProbabilityShape r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch):

    let p:=initialIndexDensity (Fin qCount) D*rsv/2
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D
    let q:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1)
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1)
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
    1-lossE-χcol-χhub-χglobal-2/(n:ℝ)^q₀-(1/(n:ℝ)+2/(n:ℝ)^2)-χlocal ≤
      ((μ.sigma ρ).prod ν).probability (OrdinaryAssignedCorrectionEvent r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch) :=by
  exact h
end Oberwolfach
