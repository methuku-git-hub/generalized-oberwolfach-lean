module

public import Oberwolfach.LongResidualLossFromLocalTests

@[expose] public section
/-! Local retention controls the ordinary-spoke mismatch on the same
protected vertex set, uniformly for all hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance retentionMismatchLocalFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_retention_mismatch_local
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (A:Finset (Fin n)) (ζ:ℝ)
    (hrows:RetainedRestrictionLocalGood π d (fun e=>raw (Sum.inr e)) false t A Finset.univ ζ J):
    ∀w,((A.filter (fun v=>¬(retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false false v w↔
      rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤ζ*A.card :=by
  intro w
  have hsub:(A.filter (fun v=>¬(retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false false v w↔
      rawMarkedPairSpokes π d raw false false false v w)))⊆
      A.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) false t J (v,w)≠
        rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,w)):=by
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    refine ⟨hv.1,?_⟩
    intro he
    dsimp [retainedRawMarkedSpokes,rawMarkedPairSpokes,rawMarkedSpokes] at hv
    rw [he] at hv
    exact hv.2 ⟨(fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _),
      (fun h=>by convert h using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _)⟩
  have hh:((A.filter (fun v=>¬(retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false false v w↔
      rawMarkedPairSpokes π d raw false false false v w))).card:ℝ)≤
      ((A.filter (fun v=>retainedRawFamilyState π d (fun e=>raw (Sum.inr e)) false t J (v,w)≠
        rawIntervalFamilyState π d (fun e=>raw (Sum.inr e)) (v,w))).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
  apply hh.trans
  convert (hrows.1 w (Finset.mem_univ _)) using 1 <;> congr! 6 <;> exact Subsingleton.elim _ _
end Oberwolfach
