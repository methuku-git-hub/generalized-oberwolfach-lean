module

public import Oberwolfach.FirstVortexOrientedTargetCapacity
public import Oberwolfach.FirstVortexClassPrescribedAssignmentNoMarkedBudget
public import Oberwolfach.FirstVortexOrientedMatchingTargetSize
public import Oberwolfach.FirstVortexOrientedMatchingCapacity
public import Oberwolfach.FirstVortexProtectedMatchingTargetSize
public import Oberwolfach.FirstVortexProtectedMatchingCapacity
public import Oberwolfach.FirstVortexSourceMatchingTargetSize
public import Oberwolfach.FirstVortexSourceMatchingCapacity

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance firstVortexClassTargetCapacityFin (n:ℕ):DecidableEq (Fin n):=selectedAlignedSourceWithLoadFin n

theorem first_vortex_class_oriented_matching_target_and_capacity
    (ε θ ρ₀ lam:ℝ) (m d:ℕ) (hm:0<m) (hε:0<ε) (hθ:0<θ) (hθ1:θ≤1)
    (hρhi:ρ₀≤1) (hεsmall:ε≤(ρ₀/4)/80000)
    (hlam:0≤lam) (hlam1:lam≤1) (hd:0<d) (hspacing:1/(d:ℝ)≤θ/1024):
    ∃N:ℕ,∀n K:ℕ,N≤n→0<K→∀(U:Type) [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dv mm:ℕ) (β:ℝ) (Vort:Vortex U P Dv β ε mm)
    (hreg:P.IsRegularOfDegree Dv) (hDv:0<Dv) (hρ:initialIndexDensity U Dv≤1) (hmm:0<mm)
    (σE:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)
    (Del:Finset (Sym2 (Fin n))) (t:ℕ)
    (Jret:StartRetentionOutcome (rawStartHubSet π d
      (fun e=>rawExpandedApproximateCollapse (Sum.inr e) (σE (Sum.inr e))) false) t),
    let ℓ:=fun i:Fin K=>longPaddedSeedExponent i+2
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
    (a γ ζ:ℝ) (hγ:0≤γ) (ha:a≤lam/(10*d)) (hγcap:γ≤lam/(10*d))
    (hζ:ζ≤θ/4096) (hζ0:0≤ζ)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrows:RetainedRestrictionLocalGood π d σ false t A H ζ Jret)
    (hfixed:∀w∈H,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈A,|rawIntervalUnassignedColumnCount π d σ v H-
      ∑w∈H,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ))
    (Kbad Used:SimpleGraph (Fin n)) (absorber:U→Finset (Fin n)) (δ:ℝ) (hU:0<Fintype.card U)
    (Sclass DelG:SimpleGraph (Fin n)) (bmatch lamAssign:ℝ) (eps α:ℝ) (hK3:3≤K) (hθmax:θ≤1/100) (heps0:0≤eps)
    (hρ₀:0<ρ₀) (hα:0<α) (hlamθ:lam≤θ)
    (hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)))
    (hαsmall:α/16≤((ρ₀/4)/40000)*θ/1024)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (hdisj:∀c∈M,∀c'∈M,c≠c'→Disjoint (Q c) (Q c'))
    (hcounts:∀w g,|rawIntervalHubStartCount π d g σ w-
      (n:ℝ)*longAssignedIntervalProbability F hF K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hsourceCount:LongMatchingSourceCountWitness F hF π d m ℓ θ eps T (M.map q))
    ,
    LongSelectedOrientedSourceWithLoadAndMatching hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ (FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lamAssign) (M.map q) →
    LongSelectedOrientedSourceWithLoadMatchingCapacity hU F P π d m ℓ raw t Jret σE H A Kbad Used absorber δ
      (fun occupied Pack=>(FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lamAssign) occupied Pack ∧ ∀w,
        ((innerRequiredTargets H A (rawReservedSpokeList π d σ)
          (retainedFinalMarkedAt π d σ t Jret) absorber occupied w).card:ℝ)≤(θ/1024)*n) ρ₀ (M.map q) :=by
  obtain ⟨N,hN⟩:=first_vortex_oriented_matching_target_and_capacity ε θ ρ₀ lam m d hm hε hθ hθ1 hρhi hεsmall hlam hlam1 hd hspacing
  refine ⟨N,?_⟩
  intro n K hn hK U _ _ P π Dv mm β Vort hreg hDv hρ hmm σE Del t Jret ℓ raw H A σ R T S hST q Q M F hF a γ ζ hγ ha hγcap hζ hζ0 hmatch hrows hfixed hcolumn Kbad Used absorber δ hU Sclass DelG bmatch lamAssign eps α hK3 hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hnoshort hdisj hcounts hsourceCount hsource
  have hh:=hN n K hn hK
  have hdec:firstVortexOrientedTargetCapacityFin n=firstVortexClassTargetCapacityFin n:=Subsingleton.elim _ _
  have hdecK:firstVortexOrientedTargetCapacityFin K=firstVortexClassTargetCapacityFin K:=Subsingleton.elim _ _
  try rw [hdec] at hh
  try rw [hdecK] at hh
  refine hh U P π Dv mm β Vort hreg hDv hρ hmm σE Del t Jret M F hF a γ ζ hγ ha hγcap hζ hζ0 hmatch hrows hfixed hcolumn Kbad Used absorber δ hU
    (FirstVortexClassPrescribedAssignmentNoMarkedBudget P Sclass DelG Used Kbad A π d σE t Jret H α bmatch ρ₀ θ ε lamAssign)
    eps α hK3 hθmax heps0 hρ₀ hα hlamθ hepsAssign hαsmall hnoshort hdisj hcounts hsourceCount ?_ hsource
  intro Old Pack h v
  exact h.1 v
end Oberwolfach
