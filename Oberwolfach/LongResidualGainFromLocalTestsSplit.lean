module

public import Oberwolfach.ResidualSpokeLocalGain
public import Oberwolfach.LongAllHubLocalRequiredTargets

@[expose] public section
/-! The local gain in ordinary spokes is controlled by the same local
unassigned and retention tests used by the first-vortex sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_residual_gain_from_local_tests_split
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U] (hn:0<n) (hK:0<K)
    (m d:ℕ) (hm:0<m) (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (θ:ℝ) (hθ:0≤θ) (hθ1:θ≤1) (π:Equiv.Perm (Fin n))
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) t)
    (A:Finset (Fin n)) (R occupied unused:U→Finset (Fin n))
    (happrox:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inl true)→x∈occupied w)
    (hordinary:∀w x,rawIntervalFamilyState π d σ (x,w)=some (Sum.inr true)→x∈occupied w ∨ x∈unused w)
    (ζ:ℝ) (hrows:RetainedRestrictionLocalGood π d σ false t A Finset.univ ζ J)
    (hfixed:∀w,|rawIntervalUnassignedHubCountOn π d σ w A-
      (A.card:ℝ)*(1-(∑g,longAssignedIntervalProbability F hF K m θ w g)-
        (∑j,longAssignedSpokeProbability F hF K m θ w j))|<(A.card:ℝ)^(3/4:ℝ)):
    let Y:=retainedFinalMarkedAt π d σ t J
    let Hold:=fun w=>Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ false t J false false false v w);
    (∀w,Disjoint (R w\Y w) (occupied w))→
    ∀w,((A∩((R w\Y w)\Hold w)).card:ℝ)≤
      2*θ*A.card+(A.card:ℝ)^(3/4:ℝ)+2*ζ*A.card+((unused w∩A).card:ℝ) :=by
  intro Y Hold hOld w
  let L:=rawReservedSpokeList π d σ
  let Target:=A\(L w∪Y w∪occupied w)
  let Mismatch:=A∩(L w\Hold w)
  have htarget:=long_all_hub_local_required_targets hn hK m d hm F hF θ hθ hθ1 π σ t J
    A occupied unused happrox hordinary ζ hrows hfixed w
  have htarget':(Target.card:ℝ)≤2*θ*A.card+(A.card:ℝ)^(3/4:ℝ)+ζ*A.card+((unused w∩A).card:ℝ):=by
    simpa only [Target,L,Y] using htarget
  have hmis:Mismatch⊆A.filter (fun v=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w)):=by
    intro v hv
    have hmem:v∈A ∧ v∈L w ∧ v∉Hold w:=by
      simpa only [Mismatch,Finset.mem_inter,Finset.mem_sdiff] using hv
    obtain ⟨hA,hL,hnot⟩:=hmem
    apply Finset.mem_filter.mpr
    refine ⟨hA,?_⟩
    have hraw:rawIntervalFamilyState π d σ (v,w)=some (Sum.inr false):=by
      simpa only [L,rawReservedSpokeList,rawIntervalOrdinaryOuter,Finset.mem_filter,Finset.mem_univ,true_and] using hL
    have hnot':retainedRawFamilyState π d σ false t J (v,w)≠some (Sum.inr false):=by
      simpa only [Hold,Finset.mem_filter,Finset.mem_univ,true_and,retainedRawMarkedSpokes] using hnot
    intro he
    exact hnot' (he.trans hraw)
  have hmiscard:(Mismatch.card:ℝ)≤ζ*A.card:=by
    have hh:=(Finset.card_le_card hmis)
    have hh':(Mismatch.card:ℝ)≤((A.filter (fun v=>retainedRawFamilyState π d σ false t J (v,w)≠rawIntervalFamilyState π d σ (v,w))).card:ℝ):=by exact_mod_cast hh
    apply hh'.trans
    convert (hrows.1 w (Finset.mem_univ _)) using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  have hgain:((A∩((R w\Y w)\Hold w)).card:ℝ)≤Target.card+Mismatch.card:=by
    exact_mod_cast (residual_spoke_local_gain A (L w) (Y w) (occupied w) (R w) (Hold w) (hOld w)).2
  linarith
end Oberwolfach
