module

public import Oberwolfach.LongRetentionMismatchFromGlobalEvent
public import Oberwolfach.LongResidualSpokeCompletionControl

@[expose] public section
/-! For an arbitrary hub set, the actual ordinary-spoke changes split into
retention mismatches, completion-image losses and new residual spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance restrictedSpokeChangeFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_restricted_spoke_change
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (B:Finset U) (R C:U→Finset (Fin n)) (ζ load gain:ℝ)
    (hζ:0≤ζ) (hU:Fintype.card U≤n)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    let Y:=fun w=>markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false;
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)→
    (∀v,((B.filter (fun w=>v∈C w)).card:ℝ)≤load)→
    (∀v,((B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d raw false false false v w)).card:ℝ)≤gain)→
    ∀v,(∑w∈B,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0)≤ζ*n+load+gain :=by
  intro Y H hprotect hload hgain v
  have hmismatch:= (long_retention_mismatch_from_global_event π d raw false false false t J ζ hζ (by simpa using hU) hgood).1 false v
  have hsub:B.filter (fun w=>¬(H false v w↔v∈R w\Y w)) ⊆
      (Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))) ∪
      ((B.filter (fun w=>v∈C w)) ∪
       (B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d raw false false false v w))) :=by
    intro w hw
    have ⟨hwB,hchange⟩:=Finset.mem_filter.mp hw
    by_cases he:H false v w↔rawMarkedPairSpokes π d raw false false false v w
    · by_cases hr:v∈R w\Y w
      · have hn:¬rawMarkedPairSpokes π d raw false false false v w:=by
          intro hraw
          exact hchange ⟨fun _=>hr,fun _=>he.mpr hraw⟩
        exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hwB,hr,hn⟩))
      · have hh:H false v w:=by
          by_contra hh
          exact hchange ⟨fun h=>False.elim (hh h),fun h=>False.elim (hr h)⟩
        have hl:v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w:=by
          have hraw:=he.mp hh
          simpa only [rawMarkedPairSpokes,rawMarkedSpokes,rawReservedSpokeList,rawIntervalOrdinaryOuter,
            Finset.mem_filter,Finset.mem_univ,true_and] using hraw
        have hc:v∈C w:=by
          by_contra hc
          exact hr (hprotect w v hl hc)
        exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwB,hc⟩))
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩)
  have hcard:((B.filter (fun w=>¬(H false v w↔v∈R w\Y w))).card:ℝ)≤
      ((Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)+
      ((B.filter (fun w=>v∈C w)).card:ℝ)+
      ((B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d raw false false false v w)).card:ℝ):=by
    have hh₁:=Finset.card_le_card hsub
    have hh₂:=Finset.card_union_le
      (Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w)))
      ((B.filter (fun w=>v∈C w)) ∪
       (B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d raw false false false v w)))
    have hh₃:=Finset.card_union_le (B.filter (fun w=>v∈C w))
      (B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d raw false false false v w))
    have hh : (B.filter (fun w=>¬(H false v w↔v∈R w\Y w))).card ≤
      (Finset.univ.filter (fun w=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card +
      (B.filter (fun w=>v∈C w)).card +
      (B.filter (fun w=>v∈R w\Y w ∧ ¬rawMarkedPairSpokes π d raw false false false v w)).card := by omega
    exact_mod_cast hh
  have hsum:(∑w∈B,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0)=
      ((B.filter (fun w=>¬(H false v w↔v∈R w\Y w))).card:ℝ):=by
    simp only [Finset.sum_ite,Finset.sum_const_zero,add_zero,Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum]
  simp only [Fintype.card_fin] at hmismatch
  linarith [hload v,hgain v]
end Oberwolfach
