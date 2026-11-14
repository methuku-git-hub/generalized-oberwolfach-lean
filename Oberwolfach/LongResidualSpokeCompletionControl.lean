module

public import Oberwolfach.LongFactorResidualSpokePartition
public import Oberwolfach.RawReservedSpokeList

@[expose] public section
/-! Record the actual completion images that can consume reserved spokes,
with uniform row and column bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance residualSpokeCompletionControlFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

def LongResidualSpokeCompletionControl
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (R:U→Finset (Fin n)) (θ δ:ℝ):Prop:=
  let Y:=fun w=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
  ∃C:U→Finset (Fin n),
    (∀v,((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤δ*n+(Real.sqrt δ*n+1)) ∧
    (∀w,((C w).card:ℝ)≤10*θ*n) ∧
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)
end Oberwolfach
