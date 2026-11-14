module

public import Oberwolfach.OrdinaryAssignedCorrectionPreparationInputs

@[expose] public section
/-! The coherent matching core retained by the common event supplies the
start-count tests, with the original assigned sampling probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_event_matching_starts
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
    (seed:(Fin (mMatch+1)→Fin n)→ℝ) (tMatch ξMatch:ℝ)
    (z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→Bool))
    (hBad:Bad=permutationConflictGraph π (3*d))
    (hz:OrdinaryAssignedCorrectionEvent r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π
      F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath
      Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch z):
    let qprob:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1);
    (∀u,(∑g:Bool,qprob u g)≤ 1/8) ∧
    (∀u g,|rawIntervalHubStartCount π d g (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (z.1.1 (Sum.inr e))) u-
      (n:ℝ)*qprob u g/d|<(n:ℝ)^(3/4:ℝ)/d) :=by
  intro qprob
  have hh:=ordinary_assigned_correction_preparation_inputs r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π
    F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath
    Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch z hBad hz
  have hprior:=hh.1
  unfold OrdinaryOriginalMatchingBalanceFamilyPrior at hprior
  have hextra:=hprior.1.1.1.1.2
  unfold OrdinaryRecodedMatchingExtra at hextra
  have hcore:=hextra.1
  unfold OrdinaryShiftedMatchingCoreEvent at hcore
  exact ⟨sampling.hQ,hcore.2.2.2⟩
end Oberwolfach
