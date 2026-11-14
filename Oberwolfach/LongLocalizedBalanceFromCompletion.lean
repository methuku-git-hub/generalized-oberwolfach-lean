module

public import Oberwolfach.MarkedInnerBalanceLocalizedChanges
public import Oberwolfach.MarkedRestrictedDegreeLocalPhysicalChange
public import Oberwolfach.LongResidualRestrictedSpokeChange

@[expose] public section
/-! The finite inner balance transfers on the same retained sample and
completion. The remaining quantitative inputs are crossing rim changes,
completion-image load, new residual spokes, and the existing column loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance localizedBalanceCompletionFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_localized_balance_from_completion
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (A:Finset (Fin n)) (B:Finset U) (hA:∀x,π x∈A↔x∈A)
    (σ τ:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (R C:U→Finset (Fin n)) (DR:SimpleGraph (Fin n)) (η δR δS ζ load gain:ℝ)
    (hη:0≤η) (hδR:0≤δR) (hδS:0≤δS) (hζ:0≤ζ) (hU:Fintype.card U≤n)
    (hgood:RetainedRestrictionGood π d (fun e=>σ (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    let Y:=fun w=>markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>σ (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let H':=fun b v w=>if b then H true v w else v∈R w\Y w;
    (∀v u,¬(H false v u∧H true v u))→
    (∀v u,¬(H' false v u∧H' true v u))→
    (∀a,¬(rawMarkedPairRims P π d σ a↔rawMarkedPairRims P π d τ a)→markedPairPhysical π a∈DR.edgeFinset)→
    (∀v,((A.filter (fun x=>DR.Adj v x)).card:ℝ)≤δR)→
    (∀w v,v∈rawReservedSpokeList π d (fun e=>σ (Sum.inr e)) w→v∉C w→v∈R w\Y w)→
    (∀v,((B.filter (fun w=>v∈C w)).card:ℝ)≤load)→
    (∀v,((B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d σ false false false v w)).card:ℝ)≤gain)→
    ζ*n+load+gain≤δS→
    (∀w,(∑v∈A,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0)≤δS)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun s:(Fin n)×U=>H false s.1 s.2∨H true s.1 s.2)
    let E':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>τ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun s:(Fin n)×U=>H' false s.1 s.2∨H' true s.1 s.2);
    (∀z i,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S m A B z i|≤η)→
    ∀z i,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
      (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' m A B z i|≤η+2*δR+(m+2:ℕ)*δS :=by
  intro Y H H' hTypes hTypes' hrim hcross hprotect hload hgain hbudget hcol E K S E' K' S' hbal
  have hr:=marked_restricted_degree_after_local_physical_changes P π d A hA σ τ DR δR hrim hcross
  have hs:=long_residual_restricted_spoke_change π d σ t J B R C ζ load gain hζ hU hgood hprotect hload hgain
  have hrow':∀b v,(∑w∈B,if ¬(H b v w↔H' b v w) then (1:ℝ) else 0)≤δS:=by
    intro b v
    cases b
    · simpa only [H',Bool.false_eq_true,ite_false] using (hs v).trans hbudget
    · simpa only [H',ite_true,iff_self,not_true,ite_false,Finset.sum_const_zero] using hδS
  have hcol':∀b w,(∑v∈A,if ¬(H b v w↔H' b v w) then (1:ℝ) else 0)≤δS:=by
    intro b w
    cases b
    · simpa only [H',Bool.false_eq_true,ite_false] using hcol w
    · simpa only [H',ite_true,iff_self,not_true,ite_false,Finset.sum_const_zero] using hδS
  have hres:=marked_inner_balance_with_localized_changes P π d m A B η δR δS hη hδR hδS σ τ H H' hTypes hTypes' hr
    (by convert hrow' using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hcol' using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
    (by convert hbal using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _)
  dsimp only [S'] at ⊢
  convert hres using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
end Oberwolfach
