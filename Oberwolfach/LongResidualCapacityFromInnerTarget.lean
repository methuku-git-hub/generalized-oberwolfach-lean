module

public import Oberwolfach.LongResidualMissingFromMatching
public import Oberwolfach.LongActualResidualMissingBound
public import Oberwolfach.LongResidualPrescribedFromMatching
public import Oberwolfach.LongAssignedRootCountUpper
public import Oberwolfach.LongResidualPrescribedFromCounts
public import Oberwolfach.ResidualMatchingCapacityAtOrder
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
local instance longActualResidualCapacityInnerFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_actual_residual_capacity_from_inner_target_row
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (hn:0<n) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (hd:1≤d) (hm:0<m)
    (Fam:U→SimpleGraph (Fin n)) (hFam:∀w,(Fam w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0<θ) (hθ1:θ≤1)
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
    (hmatch:∀i,((longRawIncidenceSet S i\M.biUnion Q).card:ℝ)≤max (α*n) (γ*(longRawIncidenceSet S i).card))
    (αCap b z:ℝ) (hαCap:0<αCap) (hb:0≤b)
    (hbudget:16/(d:ℝ)+16*max α γ+16*b/αCap+4*z≤θ/8)
    (hsmall:32*(n:ℝ)^(3/4:ℝ)/(d:ℝ)+18≤θ*n/8),
    let A:=retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t Jret w
    let B:={x:Fin n // rawIntervalColouredStart π d (fun e=>raw (Sum.inr (w,e))) x true}
    let Marked:=longRawMarkedWheelsAtHub P π d m ℓ raw true true (M.map q) w
    ∀{J:Type} [DecidableEq J]
    (a:ActualResidualData (K:=A⊕B) (J:=J) (Fam w))
    (G:SimpleGraph (Fin n)) (Z:Finset (Fin n))
    (hrem:θ*n/4≤(a.remaining.card:ℝ))
    (hdegree:∀v,(G.degree v:ℝ)≤b*n)
    (I:Finset (Fin n)) (ε η ζ:ℝ) (hI:(I.card:ℝ)≤ε*n)
    (hsub:(n:ℝ)^(3/4:ℝ)≤η*n) (hZrow:(Z.card:ℝ)≤2*θ*I.card+(n:ℝ)^(3/4:ℝ)+ζ*n+max α γ*n)
    (hZcoeff:2*θ*ε+η+ζ+max α γ≤z)
    (hcounts:∀g,|rawIntervalHubStartCount π d g (fun e=>raw (Sum.inr e)) w-
      (n:ℝ)*longAssignedIntervalProbability Fam hFam K m θ w g/(d:ℝ)|<(n:ℝ)^(3/4:ℝ)/(d:ℝ))
    (hs₁:a.s₁=firstSumIndices)
    (hd':a.d=d) (hs:a.s₂=secondSumIndices)
    (hpositions:∀b:B,a.T (.inr b)=packedPhysicalSpokePositions _ _ _ _ m (3*d) d π
      (rawMarkedPairSpokes π d raw true true false) (rawMarkedPairSpokes π d raw true true true) Marked w b.val),
    8*(residualSubtypeSet a.remaining a.prescribed).card+
      8*⌈4*(G.edgeFinset.card:ℝ)/(αCap*Fintype.card (Fin n))⌉₊+4*Z.card+10≤
      Fintype.card {x // x∈a.remaining}:=by
  intro R T S hST q Q M w α γ hγ hmatch αCap b z hαCap hb hbudget hsmall A B Marked J _ a G Z hrem hdegree I ε η ζ hI hsub hZrow hZcoeff hcounts hs₁ hd' hs hpositions
  have hp:=long_actual_residual_prescribed_from_common_counts hn P π d m hd hm Fam hFam θ hθ.le hθ1 hnoshort ℓ raw t Jret Del M w α γ hγ hmatch a hcounts hs₁ hd' hs hpositions
  have hcap:=residual_matching_capacity_at_order d (by omega) θ αCap b (max α γ) z hθ hαCap hb hbudget n hn hsmall
  have hdec:longActualResidualCapacityInnerFin n=instDecidableEqFin n:=Subsingleton.elim _ _
  rw [←hdec] at hcap
  have hIZ:2*θ*(I.card:ℝ)≤2*θ*(ε*n):=mul_le_mul_of_nonneg_left hI (by positivity)
  have hscale:=mul_le_mul_of_nonneg_right hZcoeff (Nat.cast_nonneg n)
  have hZ:(Z.card:ℝ)≤z*n:=by nlinarith
  exact hcap a.remaining a.prescribed G Z hrem hp hdegree hZ
end Oberwolfach
