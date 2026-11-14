module

public import Oberwolfach.LongResidualMissingFromMatching
public import Oberwolfach.LongActualResidualMissingBound
public import Oberwolfach.LongResidualPrescribedFromMatching
public import Oberwolfach.LongAssignedRootCountUpper
public import Oberwolfach.ResidualActualPrescribedCount
public import Oberwolfach.ActualResidualMissingSum
public import Oberwolfach.LongRawMatchingIncidenceBounds

@[expose] public section
/-! Discharge the actual residual's missing-position bound from the common
matching event, with the original sampling outcome and deletion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longActualResidualPrescribedCountsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_residual_prescribed_from_common_counts
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d) (hm:0<m)
    (Fam:U→SimpleGraph (Fin n)) (hFam:∀w,(Fam w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1)
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (ℓ:Fin K→ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (Jret:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (Del:Finset (Sym2 (Fin n))):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P π d raw true true)
    let S:=longRawSurvivingResources P π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))) (w:U)
    (α γ:ℝ) (hγ:0≤γ)
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (α*n) (γ*(longRawIncidenceSet S i).card)),
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    ∀{J:Type} [DecidableEq J]
    (a:ActualResidualData (K:=A⊕B) (J:=J) (Fam w))
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability Fam hFam K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hs₁:a.s₁=firstSumIndices)
    (hd':a.d=d) (hs:a.s₂=secondSumIndices)
    (hpositions:∀b:B,a.T (.inr b)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w b.val),
    ((residualSubtypeSet a.remaining a.prescribed).card:ℝ)≤
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ)+2*max α γ*n:=by
  intro R T S hST q Q M w α γ hγ hmatch A B Marked J _ a hcounts hs₁ hd' hs hpositions
  have hp:=long_actual_residual_prescribed_from_matching P π d m hd hnoshort ℓ raw t Jret Del M w α γ hγ hmatch a (hFam w) hs₁ hd' hs hpositions
  have hth:=long_assigned_root_count_upper (K:=K) hn m d hm (by omega) Fam hFam θ hθ hθ1 π
  have hdec:longActualResidualPrescribedCountsFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hth
  have hroot:=hth (fun e=>raw (Sum.inr e)) t Jret w hcounts
  have hroot':(Fintype.card (A⊕B):ℝ)≤((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ):=by
    simpa only [retainedAndRawIntervalIndex] using hroot
  have heq:2*(((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ))=
      2*((n:ℝ)+2*(n:ℝ)^(3/4:ℝ))/(d:ℝ):=by ring
  nlinarith [heq]
end Oberwolfach
