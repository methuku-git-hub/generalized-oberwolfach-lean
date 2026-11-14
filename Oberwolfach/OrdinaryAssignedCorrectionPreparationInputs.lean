module

public import Oberwolfach.OrdinaryAssignedCorrectionEvent
public import Oberwolfach.OrdinaryCorrectedReservoirNamedWitness
public import Oberwolfach.OrdinarySharedSamplePhysicalInclusion

@[expose] public section
/-! The common matching and correction event supplies, on the identical
sample, the colour, balance and concrete reservoir inputs used by preparation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_correction_preparation_inputs
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
    let p:=initialIndexDensity (Fin qCount) D*rsv/2;
    let p₂:=ordinaryAssignedApproxRimProbability F hF i₀ rsv θ ((mMatch:ℝ)+1) D;
    let qprob:=ordinaryAssignedMarkedProbability F hF K θ ((mMatch:ℝ)+1);
    let sprob:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ ((mMatch:ℝ)+1);
    let E0:=fun _:Σσ,R σ=>True;
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ ((mMatch:ℝ)+1) D π d mMatch seed;
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ ((mMatch:ℝ)+1) D (ordinaryEligibleHost P π d) π d w;
    let Core:=OrdinaryShiftedMatchingCoreEvent (ordinaryEligibleHost P π d) π d mMatch p₂ 0 qprob sprob wM wO tMatch ξMatch;
    let Prior:=OrdinaryOriginalMatchingBalanceFamilyPrior P π d mMatch F hF Cres i₀ rsv θ lamMatch aRow γrow
      p smin σbal aEvent ζDel lamList bMatch qprob sprob E0 Core;
    let raw:=fun e=>expandedOrdinarySelectedCollapse e (z.1.1 e);
    let Reference:=longPhysicalStateGraph P z.1.1 {0}\Bad;
    let Href:=rawWheelSpokes π d raw false;
    Prior z.1 ∧
    (∀c:Fin 6,∀x∈Z,
      |(((P.neighborFinset x∩Z).filter (fun y=>(z.1.1 (Sum.inl s(x,y))).1=c)).card:ℝ)-
        markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*(P.neighborFinset x∩Z).card|<ζlocal*Z.card) ∧
    (∀v∈Z,|rawIntervalUnassignedColumnCount π d (fun e=>z.1.1 (Sum.inr e)) v Htest-
      ∑w∈Htest,(1-(∑g,qprob w g)-(∑j,sprob w j))|<(Z.card:ℝ)^(3/4:ℝ)) ∧
    (∀w∈Htest,|rawIntervalUnassignedHubCountOn π d (fun e=>z.1.1 (Sum.inr e)) w Z-
      (Z.card:ℝ)*(1-(∑g,qprob w g)-(∑j,sprob w j))|<(Z.card:ℝ)^(3/4:ℝ)) ∧
    OrdinaryZeroRetentionEvent π d false z.1.1 ∧
    (∀c x,|(sampledColourDegree P (fun e=>(z.1.1 (Sum.inl e)).1) c x:ℝ)-
      markedExpandedPhysicalProbability p 0 p₂ 0 sampling.u c*P.degree x|<(n:ℝ)^(3/5:ℝ)) ∧
    (∀v,|((Reference.degree v:ℝ)-2*((Finset.univ.filter (Href v)).card:ℝ))|≤
      σbal*n+2*(σbal*n)+2*((3*d:ℕ):ℝ)) ∧
    (∀w,|((Finset.univ.filter (fun v=>Href v w)).card:ℝ)-rsv*n|≤σbal*n) ∧
    ∃(Kabs:Finset (Sym2 (Fin n)⊕(Fin n×Fin qCount))) (JQ:SimpleGraph (Fin n)) (JH:Fin n→Fin qCount→Prop),
      OrdinaryCorrectedProtectedReservoirWitness r mAbs t a b ξ Reference Bad Href A Z Wterm Bterm B Kabs JQ JH :=by
  intro p p₂ qprob sprob E0 wM wO Core Prior raw Reference Href
  subst Bad
  dsimp only [OrdinaryAssignedCorrectionEvent] at hz
  obtain ⟨hlocal,⟨⟨⟨⟨hprior,hcolumn⟩,hhub⟩,hzero⟩,hglobal⟩,hres⟩:=hz
  have hpriorKeep:=hprior
  unfold OrdinaryOriginalMatchingBalanceFamilyPrior at hprior
  have hbalance:=hprior.1.1.1.2
  unfold OrdinaryReferenceBalanceColumnsEvent at hbalance
  rw [ordinary_shared_sample_reference_graph_eq_state_zero P z.1.1] at hbalance
  obtain ⟨Kabs,JQ,JH,hw⟩:=ordinary_corrected_reservoir_has_witness r mAbs t a b ξ
    (rawWheelGraph P raw\permutationConflictGraph π (3*d)) (permutationConflictGraph π (3*d)) Href
    A Z Wterm Bterm B hres
  rw [ordinary_shared_sample_reference_graph_eq_state_zero P z.1.1] at hw
  refine ⟨hpriorKeep,hlocal,hcolumn,hhub,hzero,hglobal,?_,?_,Kabs,JQ,JH,?_⟩
  · intro v;convert hbalance.1 v using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
  · intro u;exact (hbalance.2 u).le
  · convert hw using 1 <;> congr! 10 <;> first | rfl | simp | exact Subsingleton.elim _ _
end Oberwolfach
