module

public import Oberwolfach.LongResidualMissingFromMatching
public import Oberwolfach.LongActualResidualMissingBound
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
local instance longActualResidualPrescribedFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_residual_prescribed_from_matching
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d)
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
    ∀{F:SimpleGraph (Fin n)} {J:Type} [DecidableEq J]
    (a:ActualResidualData (K:=A⊕B) (J:=J) F)
    (hF:F.IsRegularOfDegree 2)
    (hs₁:a.s₁=firstSumIndices)
    (hd':a.d=d) (hs:a.s₂=secondSumIndices)
    (hpositions:∀b:B,a.T (.inr b)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w b.val),
    ((residualSubtypeSet a.remaining a.prescribed).card:ℝ)≤
      2*(Fintype.card (A⊕B):ℝ)+2*max α γ*n:=by
  intro R T S hST q Q M w α γ hγ hmatch A B Marked F J _ a hF hs₁ hd' hs hpositions
  have hm:=long_actual_residual_missing_from_matching P π d m hd hnoshort ℓ raw t Jret Del M w α γ hγ hmatch a hd' hs hpositions
  have hp:=actual_residual_prescribed_le_starts_and_missing hF a
  have h1:a.s₁.card=Fintype.card A:=by
    rw [hs₁]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (firstSumIndexEquiv (A:=A) (B:=B))).symm
  have h2:a.s₂.card=Fintype.card B:=by
    rw [hs]
    simpa only [Fintype.card_coe] using (Fintype.card_congr (secondSumIndexEquiv (A:=A) (B:=B))).symm
  rw [h1,h2,←Fintype.card_sum] at hp
  have hpR:((residualSubtypeSet a.remaining a.prescribed).card:ℝ)≤
      2*(Fintype.card (A⊕B):ℝ)+2*((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):=by exact_mod_cast hp
  linarith
end Oberwolfach
