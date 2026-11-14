module

public import Oberwolfach.LongResidualRestrictedSpokeSizeOnRoots

@[expose] public section
/-! At outside roots, global balance turns a small one-sided loss and a
small rim change into a small ordinary-spoke change on every hub subset. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance outsideSpokeChangesGlobalBalanceFin (n:ℕ):DecidableEq (Fin n):=factorRootsFin n

theorem long_outside_spoke_changes_from_global_balance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (raw:RawMarkedOutcome (Fin n) U Bool Bool)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>raw (Sum.inr e)) false) t)
    (I:Finset (Fin n)) (R C:U→Finset (Fin n)) (ζ load εrim δrim:ℝ)
    (hζ:0≤ζ) (hU:Fintype.card U≤n)
    (hgood:RetainedRestrictionGood π d (fun e=>raw (Sum.inr e)) false t
      (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζ J):
    let Y:=fun w=>markedIntervalRootSet π
      (fun _:retainedMarkedIndex π d (fun e=>raw (Sum.inr e)) false t J w=>d) Subtype.val
    let H:=retainedRawMarkedSpokes π d (fun e=>raw (Sum.inr e)) false t J false false;
    (∀w v,v∈rawReservedSpokeList π d (fun e=>raw (Sum.inr e)) w→v∉C w→v∈R w\Y w)→
    (∀v,v∉I→((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤load)→
    ∀oldRim newRim:Fin n→ℝ,
    (∀v,v∉I→|oldRim v-(((Finset.univ.filter (fun w=>H false v w)).card:ℝ)+
      ((Finset.univ.filter (fun w=>H true v w)).card:ℝ))|≤εrim)→
    (∀v,v∉I→newRim v=((Finset.univ.filter (fun w=>v∈R w\Y w)).card:ℝ)+
      ((Finset.univ.filter (fun w=>H true v w)).card:ℝ))→
    (∀v,v∉I→newRim v-oldRim v≤δrim)→
    ∀(B:Finset U) v,v∉I→
      (∑w∈B,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0)≤2*(ζ*n+load)+(εrim+δrim) :=by
  intro Y H hprotect hload oldRim newRim hOld hNew hRim
  let Roots:Finset (Fin n):=Finset.univ\I
  have hload':∀v∈Roots,((Finset.univ.filter (fun w=>v∈C w)).card:ℝ)≤load:=by
    intro v hv
    exact hload v (Finset.mem_sdiff.mp hv).2
  have hsize:∀v∈Roots,((Finset.univ.filter (fun w=>v∈R w\Y w)).card:ℝ)-
      ((Finset.univ.filter (fun w=>H false v w)).card:ℝ)≤εrim+δrim:=by
    intro v hv
    have hnot: v∉I:=(Finset.mem_sdiff.mp hv).2
    have hOld':=(abs_le.mp (hOld v hnot)).2
    have hNew':=hNew v hnot
    have hRim':=hRim v hnot
    linarith
  have hfull:=long_residual_restricted_spoke_change_from_size_on_roots π d raw t J Finset.univ Roots R C ζ load (εrim+δrim)
    hζ hU hgood hprotect hload' hsize
  intro B v hv
  have hv':v∈Roots:=Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩
  calc
    _ ≤ ∑w:U,if ¬(H false v w↔v∈R w\Y w) then (1:ℝ) else 0:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B) (by intro w _ _;split_ifs <;> norm_num)
    _ ≤ _ :=hfull v hv'
end Oberwolfach
