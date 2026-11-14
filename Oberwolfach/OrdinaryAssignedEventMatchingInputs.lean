module

public import Oberwolfach.OrdinaryAssignedCorrectionPreparationInputs
public import Oberwolfach.OrdinaryEmptyRetentionOutcome

@[expose] public section
/-! One assigned correction event retains all matching, boundary, colour and
local hub tests required to place complements on the same physical sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_event_matching_inputs
    (r d mAbs a b t q₀ n qCount K D:ℕ) (hd:2≤ d)
    (ζlocal χlocal χglobal χhub χcol ξ:ℝ)
    (P Bad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (F:Fin qCount→ SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (i₀:Fin K) (rsv θ ρ₀ smin:ℝ) (mMatch:ℕ)
    (sampling:OrdinaryAssignedVortexExactSamplingData (D:=D) F hF K i₀ rsv θ ((mMatch:ℝ)+1) ρ₀ smin d)
    (A Z Wterm:Finset (Fin n)) (Bterm B Htest:Finset (Fin qCount))
    (R:(∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e)→ Type)
    [∀σ,Fintype (R σ)] (ρ:∀σ,FiniteLaw (R σ))
    (ζ χpair χlist χbal χbd χnbr χpairR χpath:ℝ)
    (Cres:∀u,Finset (F u).ConnectedComponent)
    (lamMatch aRow γrow σbal aEvent ζDel lamList bMatch:ℝ)
    (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ ℝ)
    (seed:(Fin (mMatch+1)→ Fin n)→ ℝ) (tMatch ξMatch:ℝ)
    (z:(Σσ:∀e:RawWheelCoordinate (Fin n) (Fin qCount),RawExpandedMarkedCoordinateState Bool Bool e,R σ)×(Sym2 (Fin n)→ Bool))
    (hBad:Bad=permutationConflictGraph π (3*d))
    (hz:OrdinaryAssignedCorrectionEvent r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π
      F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath
      Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch z):
    let p:=initialIndexDensity (Fin qCount) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D;
    let qprob:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1);
    let sprob:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1);
    let J:=ordinaryEmptyRetentionOutcome (rawStartHubSet π d (fun e=>z.1.1 (Sum.inr e)) false);
    OrdinaryZeroRetentionEvent π d false z.1.1 ∧
    OrdinaryBoundaryStartEvent π d z.1.1 ∧
    OrdinaryReservedCompletionTests P π d p smin sprob z.1.1 ∧
    (∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1.1 (Sum.inr e)) w Z-
      (Z.card:ℝ)*(1-(∑g,qprob w g)-(∑j,sprob w j))|<(Z.card:ℝ)^(3/4:ℝ)) ∧
    (∀c:Fin 6,∀x∈Z,
      |(((P.neighborFinset x∩Z).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Z).card|≤ ζlocal*Z.card) ∧
    (∀Del:SimpleGraph (Fin n),(∀v,(Del.degree v:ℝ)≤ bMatch*n)→
      OrdinarySelectedMatchingFamilyLocalOccupancyResult F hF Cres i₀ rsv θ lamMatch aRow γrow mMatch d π P Del Z z.1.1 0 J) :=by
  intro p p₂ qprob sprob J
  have hh:=ordinary_assigned_correction_preparation_inputs r d mAbs a b t q₀ n qCount K D hd ζlocal χlocal χglobal χhub χcol ξ P Bad π
    F hF i₀ rsv θ ρ₀ smin mMatch sampling A Z Wterm Bterm B Htest R ρ ζ χpair χlist χbal χbd χnbr χpairR χpath
    Cres lamMatch aRow γrow σbal aEvent ζDel lamList bMatch w seed tMatch ξMatch z hBad hz
  obtain ⟨hprior,hlocal,_hcolumn,hhub,hzero,_hglobal,_hbalance,_hcolumns,_K,_JQ,_JH,_hw⟩:=hh
  unfold OrdinaryOriginalMatchingBalanceFamilyPrior at hprior
  refine ⟨hzero,hprior.1.1.2,hprior.1.2,hhub,?_,?_⟩
  · intro c x hx; exact (hlocal c x hx).le
  · intro Del hDel; exact hprior.2 Del hDel Z 0 J
end Oberwolfach
