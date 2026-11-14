module

public import Oberwolfach.LongResidualMissingFromMatching
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
local instance longActualResidualMissingFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_residual_missing_from_matching
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
    (hd':a.d=d) (hs:a.s₂=secondSumIndices)
    (hpositions:∀b:B,a.T (.inr b)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w b.val),
    (((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤max α γ*n:=by
  intro R T S hST q Q M w α γ hγ hmatch A B Marked F J _ a hd' hs hpositions
  have hm:=long_residual_missing_positions_le_uncovered_incidence P π d m hd hnoshort ℓ raw t Jret Del M w (Finset.univ:Finset B)
  have hsum:=actual_residual_missing_sum_second_indices a hs
  have hh:((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ)≤
      (longRawIncidenceSet S (.inr (true,.inr w))\M.biUnion Q).card:=by
    rw [hsum]
    simpa only [hd',hpositions] using hm
  have hhR:(((∑i∈a.s₂,(a.d-(a.T i).card)):ℕ):ℝ)≤
      ((longRawIncidenceSet S (.inr (true,.inr w))\M.biUnion Q).card:ℝ):=by exact_mod_cast hh
  have hcard:((longRawIncidenceSet S (.inr (true,.inr w))).card:ℝ)≤n:=by
    exact_mod_cast long_raw_hub_spoke_incidence_card_le S true w
  have hn:(0:ℝ)≤n:=by positivity
  have hlin:=hmatch (.inr (true,.inr w))
  apply hhR.trans
  apply hlin.trans
  apply max_le
  · exact mul_le_mul_of_nonneg_right (le_max_left α γ) hn
  · exact (mul_le_mul_of_nonneg_left hcard hγ).trans
      (mul_le_mul_of_nonneg_right (le_max_right α γ) hn)
end Oberwolfach
