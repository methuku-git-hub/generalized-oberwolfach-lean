module

public import Oberwolfach.PhysicalSampledMatchingRows

@[expose] public section
/-! Small physical rows are already within an absolute residual budget;
matching only needs to test rows above the required linear threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W Row:Type} [Fintype W] [Fintype Row] [DecidableEq W]

def LargeMatchingRow (S:Row→Finset W) (n:ℕ) (α:ℝ):Type :=
  {r:Row // α*n≤(S r).card}

instance largeMatchingRowFintype (S:Row→Finset W) (n:ℕ) (α:ℝ):Fintype (LargeMatchingRow S n α):=by
  classical
  unfold LargeMatchingRow
  infer_instance

theorem large_matching_rows_control_all
    (S:Row→Finset W) (n:ℕ) (α γ:ℝ) (hγ:0≤γ)
    (hsize:∀r,(S r).card≤n) (covered:Finset W)
    (hlarge:∀r:LargeMatchingRow S n α,
      (((S r.val)\covered).card:ℝ)≤γ*(S r.val).card):
    ∀r:Row,(((S r)\covered).card:ℝ)≤max α γ*n :=by
  intro r
  by_cases hr:α*(n:ℝ)≤(S r).card
  · have hh:=hlarge ⟨r,hr⟩
    have hc:((S r).card:ℝ)≤n:=by exact_mod_cast hsize r
    have hs:=mul_le_mul_of_nonneg_left hc hγ
    have hm:γ*(n:ℝ)≤max α γ*n:=mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    exact hh.trans (hs.trans hm)
  · have hc:(((S r)\covered).card:ℝ)≤(S r).card:=by exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : (S r)\covered⊆S r)
    have hm:α*(n:ℝ)≤max α γ*n:=mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    exact hc.trans ((le_of_lt (lt_of_not_ge hr)).trans hm)
end Oberwolfach
