module

public import Oberwolfach.RetainedRawIntervalCardinality
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section
/-! Start-count concentration gives the concrete endpoint loss from deleting
retained and raw intervals from an unassigned list. -/
set_option autoImplicit false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_raw_endpoint_count_from_start_counts
    {V U Color:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (hd:0<d) (σ:RawIntervalFamilyOutcome V U Bool Color)
    (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) t) (w:U)
    (q:U→Bool→ℝ) (hQ:∑g,q w g≤1/8)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-(Fintype.card V:ℝ)*q w g/d|<
      (Fintype.card V:ℝ)^(3/4:ℝ)/d):
    (Fintype.card (retainedAndRawIntervalIndex π d σ false true t J w):ℝ)≤
      (Fintype.card V:ℝ)/(8*(d:ℝ))+2*(Fintype.card V:ℝ)^(3/4:ℝ)/d:=by
  have h0:=(abs_lt.mp (hcounts false)).2
  have h1:=(abs_lt.mp (hcounts true)).2
  have hn:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  have hq:q w false+q w true≤1/8:=by simpa [Fintype.sum_bool,add_comm] using hQ
  have hmul:=mul_le_mul_of_nonneg_left hq hn
  have hfrac:(Fintype.card V:ℝ)*(q w false+q w true)/d≤(Fintype.card V:ℝ)/(8*(d:ℝ)):=by
    apply (div_le_div_iff₀ hdR (by positivity)).2
    nlinarith
  have hraw:=retained_raw_interval_count_le_raw_counts π d σ false true t J w
  have hsum:rawIntervalHubStartCount π d false σ w+rawIntervalHubStartCount π d true σ w≤
      (Fintype.card V:ℝ)*(q w false+q w true)/d+2*(Fintype.card V:ℝ)^(3/4:ℝ)/d:=by
    calc
      _ ≤ ((Fintype.card V:ℝ)*q w false/d+(Fintype.card V:ℝ)^(3/4:ℝ)/d)+
          ((Fintype.card V:ℝ)*q w true/d+(Fintype.card V:ℝ)^(3/4:ℝ)/d):=by linarith
      _ = _:=by ring
  exact hraw.trans (hsum.trans (by linarith [hfrac]))
end Oberwolfach
