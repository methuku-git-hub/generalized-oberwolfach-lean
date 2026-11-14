module

public import Oberwolfach.LongResidualSpokeCompletionControl

@[expose] public section
/-! A small actual completion image load can be used with a separate
spoke-control parameter, independently of the embedding error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance spokeSmallImagesFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_residual_spoke_control_from_small_images
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R C:U→Finset (Fin n)) (θ load δspoke:ℝ) (hδ:0≤δspoke) (hload:load≤Real.sqrt δspoke)
    (hrow:∀v,((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤load*n+1)
    (hcol:∀w,((C w).card:ℝ)≤10*θ*n)
    (hprotect:∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→
      v∈R w\markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val):
    LongResidualSpokeCompletionControl π d raw t J R θ δspoke :=by
  refine ⟨C,?_,hcol,hprotect⟩
  intro v
  have hh:=mul_le_mul_of_nonneg_right hload (Nat.cast_nonneg n)
  have hδn:0≤δspoke*n:=mul_nonneg hδ (Nat.cast_nonneg n)
  calc
    _ ≤ load*n+1:=hrow v
    _ ≤ δspoke*n+(Real.sqrt δspoke*n+1):=by linarith only [hh,hδn]
end Oberwolfach
