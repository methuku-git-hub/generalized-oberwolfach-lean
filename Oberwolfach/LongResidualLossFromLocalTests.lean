module

public import Oberwolfach.LongResidualSpokeLocalLoss
public import Oberwolfach.RetentionRestrictionLocalEvent

@[expose] public section
/-! A local retention test and the completion image inside the first
vortex bound the one-sided loss on that vortex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualLossLocalTestsFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_loss_from_local_tests
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (A:Finset (Fin n)) (R C:U→Finset (Fin n)) (ζ B:ℝ)
    (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t A Finset.univ ζ J)
    (hC:∀w,((A∩C w).card:ℝ)≤B):
    let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false;
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)→
    ∀w,((A.filter (fun v=>H false v w∧v∉R w\Y w)).card:ℝ)≤ζ*A.card+B :=by
  intro Y H hprotect w
  have hsub:(A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w)))⊆
      A.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) false t J (v,w)≠
        rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,w)):=by
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1,?_⟩
    intro he
    dsimp [H,retainedRawMarkedSpokes,rawMarkedPairSpokes,rawMarkedSpokes] at hv
    rw [he] at hv
    exact hv.2 ⟨(fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _),
      (fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)⟩
  have hmis:((A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤ζ*A.card:=by
    have hh:((A.filter (fun v=>¬(H false v w↔rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤
        ((A.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) false t J (v,w)≠
          rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,w))).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    apply hh.trans
    convert (hrows.1 w (Finset.mem_univ _)) using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
  have hloss:=long_residual_spoke_local_loss π d raw t J R C A hprotect w
  exact hloss.trans (add_le_add hmis (hC w))
end Oberwolfach
