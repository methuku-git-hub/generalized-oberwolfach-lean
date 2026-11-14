module

public import Oberwolfach.LongInnerRequiredOccurrenceLocal
public import Oberwolfach.LongInnerRequiredTargetLocal
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

theorem long_inner_targets_from_matching_defects_local
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
    (S:Finset (LongRawHubResource n U)) (covered:Finset S) (a γ:ℝ) (hγ:0≤γ) (hu:Fintype.card U≤n)
    (hmatch:∀i,((longRawIncidenceSet S i\covered).card:ℝ)≤max (a*n) (γ*(longRawIncidenceSet S i).card))
    (hrow:∀w,(longUnusedOrdinarySpokes π d raw occupied w).card≤
      (longRawIncidenceSet S (.inr (false,.inr w))\covered).card)
    (hcol:∀v,(Finset.univ.filter (fun w=>v∈longUnusedOrdinarySpokes π d raw occupied w)).card≤
      (longRawIncidenceSet S (.inr (false,.inl v))\covered).card):
    let Z:=innerRequiredTargets inner vertices (rawReservedSpokeList π d (fun e=>raw (Sum.inr e)))
      (retainedFinalMarkedAt π d (fun e=>raw (Sum.inr e)) t J) absorber occupied
    (∀w∈inner,((Z w).card:ℝ)≤2*θ*vertices.card+(vertices.card:ℝ)^(3/4:ℝ)+ζ*vertices.card+max a γ*n) ∧
    (∀v∈vertices,((Finset.univ.filter (fun w=>v∈Z w)).card:ℝ)≤
      2*θ*inner.card+(vertices.card:ℝ)^(3/4:ℝ)+ζ*inner.card+max a γ*n):=by
  intro Z
  let unused:=longUnusedOrdinarySpokes π d raw occupied
  have hord:=long_unused_ordinary_spokes_cover π d raw occupied
  obtain ⟨hr,hc⟩:=long_unused_spoke_linear_bounds S covered unused a γ hγ hu hmatch hrow hcol
  constructor
  · intro w hw
    have hh:=long_inner_required_targets_local_bound hn hK m d hm F hF θ hθ hθ1 π (fun e=>raw (Sum.inr e)) t J inner vertices absorber occupied unused happrox hord ζ hrows hfixed w hw
    have hsub:((unused w∩vertices).card:ℝ)≤(unused w).card:=by exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    exact hh.trans (by linarith [hr w])
  · intro v hv
    have hh:=long_inner_required_occurrences_local_bound hn hK m d hm F hF θ hθ hθ1 π (fun e=>raw (Sum.inr e)) t J inner vertices absorber occupied unused happrox hord ζ hrows hcolumn v hv
    have hsub:((inner.filter (fun w=>v∈unused w)).card:ℝ)≤((Finset.univ.filter (fun w=>v∈unused w)).card:ℝ):=by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ inner))
    exact hh.trans (by linarith [hc v])
end Oberwolfach
