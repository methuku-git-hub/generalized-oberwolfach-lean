module

public import Oberwolfach.FirstVortexOrientedGlobalLoadFromBoundary
public import Oberwolfach.FirstVortexClassPrescribedAssignmentNoMarkedBudget
public import Oberwolfach.FirstVortexGlobalLoadFromBoundaryTarget
public import Oberwolfach.LongSelectedOrientedSourceWithLoadAndMatching
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceResidualCompletion
public import Oberwolfach.LongSelectedOrientedSourceCapacityUpper
public import Oberwolfach.LongSelectedOrientedSourceGlobalLoad
public import Oberwolfach.LongSelectedOrientedSourceWithMatchingCapacity
public import Oberwolfach.LongSelectedAlignedSourceGlobalLoad
public import Oberwolfach.FirstVortexTargetGlobalOccurrence
public import Oberwolfach.ActualPrescribedLoadFromInnerTargets
public import Oberwolfach.FirstVortexSourceMatchingTargetSize

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassGlobalBoundaryFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_oriented_global_load_from_boundary
    (ε θ δglobal:ℝ) (d:ℕ) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1) (hδ:0<δglobal) (hθδ:10*θ≤δglobal)
    (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (m:ℕ) (hm:0<m) (ℓ:Fin K→ℕ)
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σE e)
    let H:=Vort.extendedIndices 1
    let A:=Vort.extendedVertices 1
    let σ:=fun e=>raw (Sum.inr e)
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S))))
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (a γ ζ ρ:ℝ) (hγ:0≤γ) (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hρscale:ρ≤θ/4096) (hρscale0:0≤ρ) (hscale:max a γ*n≤ρ*A.card)
    (hboundary:∀v,((rawIntervalBoundaryHubSet π d σ Finset.univ v).card:ℝ)≤
      4*(Fintype.card U:ℝ)/d+4*(n:ℝ)^(3/4:ℝ))
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ ρ₀:ℝ) (hU:0<Fintype.card U)
    (Sclass DelG:SimpleGraph (Fin n)) (bmatch α lam:ℝ) (hαglobal:α≤4*δglobal),
    LongSelectedOrientedSourceWithMatchingCapacityUpper hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ (FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam) ρ₀ θ (M.map q) →
    LongSelectedOrientedSourceWithGlobalLoadCapacityUpper hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ (FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam) ρ₀ θ δglobal (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_oriented_global_prescribed_load_from_boundary ε θ δglobal d hε hθ hθ1 hδ hθδ hd hspacing
  refine ⟨N,?_⟩
  intro n K hn hK U _ _ P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del t Jret raw H A σ R T S hST q Q M F hF a γ ζ ρ hγ hζ hζ0 hρscale hρscale0 hscale hboundary hmatch hrows hfixed hcolumn Kbad Used absorber δ ρ₀ hU Sclass DelG bmatch α lam hαglobal hsource
  have hh:=hN n K hn hK
  have hdec:firstVortexOrientedGlobalBoundaryFin n=firstVortexClassGlobalBoundaryFin n:=Subsingleton.elim _ _
  have hdecK:firstVortexOrientedGlobalBoundaryFin K=firstVortexClassGlobalBoundaryFin K:=Subsingleton.elim _ _
  try rw [hdec] at hh
  try rw [hdecK] at hh
  refine hh U P π m hm ℓ Dv mm β Vort hreg hDv hρ hmm σE Del t Jret M F hF a γ ζ ρ hγ hζ hζ0 hρscale hρscale0 hscale hboundary hmatch hrows hfixed hcolumn Kbad Used absorber δ ρ₀ hU
    (FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lam) ?_ hsource
  intro Old Pack h v
  have hc:α/16≤δglobal/4:=by linarith
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg n
  have hm:=mul_le_mul_of_nonneg_right hc hn0
  linarith [h.1 v]
end Oberwolfach
