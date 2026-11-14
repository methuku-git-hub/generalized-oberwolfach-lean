module

public import Oberwolfach.LongInnerTargetsLocalUnusedSpokes
public import Oberwolfach.LongUnusedOrdinarySpokeLocalMatching
public import Oberwolfach.LongInnerTargetsMatchingDefectsLocal
public import Oberwolfach.LongInnerTargetsFromMatchingDefects
public import Oberwolfach.LongUnusedOrdinarySpokeFromMatching
public import Oberwolfach.LongInnerRequiredTargetBound
public import Oberwolfach.LongInnerOccurrenceFromFullColumn
public import Oberwolfach.LongUnusedOrdinarySpokeCover
public import Oberwolfach.LongUnusedSpokeLinearBounds

@[expose] public section
/-! The common row and column tests and matching defects bound required targets. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_inner_targets_from_actual_local_matching_defects
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (inner:Finset U) (vertices:Finset (Fin n)) (absorber occupied:U→Finset (Fin n))
    (happrox:∀w x,rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (x,w)=some (Sum.inl true)→x∈occupied w)
    (ζ:ℝ) (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t vertices inner ζ J)
    (hfixed:∀w∈inner,|rawIntervalUnassignedHubCountOn π d (fun e=>raw (Sum.inr e)) w vertices-
      (vertices.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(vertices.card:ℝ)^(3/4:ℝ))
    (hcolumn:∀v∈vertices,|rawIntervalUnassignedColumnCount π d (fun e=>raw (Sum.inr e)) v inner-
      ∑w∈inner,(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(vertices.card:ℝ)^(3/4:ℝ))
    (P₀:SimpleGraph (Fin n)) (ℓ:Fin K→ℕ) (Del:Finset (Sym2 (Fin n)))
    (b:ℝ):
    let R:=mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)
    let T:=bernoulliVertexSet (longRawHubState P₀ π d raw true true)
    let S:=longRawSurvivingResources P₀ π d raw true true Del
    let hST:=long_raw_surviving_resources_subset P₀ π d raw true true Del
    let q:=survivingCandidateEmbedding R S T hST
    let Q:=restrictedResourceSet R (Function.Embedding.subtype (·∈S))
    ∀(M:Finset (RestrictedResource R (Function.Embedding.subtype (·∈S)))),
    (∀w∈inner,((longLocalHubSpokeDefects S (M.biUnion Q) false w vertices).card:ℝ)≤b)→
    (∀v∈vertices,((longLocalVertexSpokeDefects S (M.biUnion Q) false v inner).card:ℝ)≤b)→
    (∀(w:U) (a:LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q)),
      (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.2=w→
      ∀v∈Finset.univ.image ((longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (·∈T)) (M.map q) a).val.1.val),v∈occupied w)→
    (∀w W,W∈longRawMarkedWheelsAtHub P₀ π d m ℓ raw true true (M.map q) w→
      ∀i:Fin (m+1),W.1.val i∈occupied w)→
    let Z:=innerRequiredTargets inner vertices (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t J) absorber occupied
    (∀w∈inner,((Z w).card:ℝ)≤2*θ*vertices.card+(vertices.card:ℝ)^(3/4:ℝ)+ζ*vertices.card+b) ∧
    (∀v∈vertices,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      2*θ*inner.card+(vertices.card:ℝ)^(3/4:ℝ)+ζ*inner.card+b):=by
  intro R T S hST q Q M hlocalRow hlocalCol hOrd hMarked Z
  obtain ⟨hrow,hcol⟩:=long_unused_ordinary_spokes_local_matching_bounds P₀ π d m ℓ raw Del M occupied inner vertices hOrd hMarked
  apply long_inner_targets_from_local_unused_spokes hn hK m d hm F hF θ hθ hθ1 π raw t J inner vertices absorber occupied happrox ζ hrows hfixed hcolumn b
  · intro w hw
    exact (Nat.cast_le.mpr (hrow w)).trans (hlocalRow w hw)
  · intro v hv
    exact (Nat.cast_le.mpr (hcol v)).trans (hlocalCol v hv)
end Oberwolfach
