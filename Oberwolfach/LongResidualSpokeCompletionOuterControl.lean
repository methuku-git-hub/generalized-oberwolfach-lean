module

public import Oberwolfach.LongResidualSpokeCompletionControl

@[expose] public section
/-! Preserve the protected completion image together with its outer-hub
local bound; this implies the original global control. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualSpokeCompletionOuterControlFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

def LongResidualSpokeCompletionOuterControl
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ:ℝ) (inner:Finset U) (A:Finset (Fin n)) (bound:ℝ):Prop:=
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
  ∃C:U→Finset (Fin n),
    (∀v,((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤δ*n+(Real.sqrt δ*n+1)) ∧
    (∀w,((C w).card:ℝ)≤10*θ*n) ∧
    (∀w∉inner,(((C w)∩A).card:ℝ)≤bound) ∧
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)

theorem long_residual_spoke_completion_outer_control_implies_global
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ:ℝ) (inner:Finset U) (A:Finset (Fin n)) (bound:ℝ)
    (h:LongResidualSpokeCompletionOuterControl π d raw t J R θ δ inner A bound):
    LongResidualSpokeCompletionControl π d raw t J R θ δ :=by
  obtain ⟨C,hrow,hcard,_,hprotect⟩:=h
  exact ⟨C,hrow,hcard,hprotect⟩
end Oberwolfach
