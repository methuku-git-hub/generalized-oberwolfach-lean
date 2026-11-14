module

public import Oberwolfach.RetainedRawIntervalCardinality

@[expose] public section
/-! Upper bound the total number of retained and raw interval roots by the
observed start counts at a hub. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_raw_interval_root_upper_general
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d c:ℕ) (hd:0<d) (hc:0<c)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool) (r:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ false) r) (w:U)
    (q:Bool→ℝ) (t:ℝ)
    (hcounts:∀g,|rawIntervalHubStartCount π d g σ w-(n:ℝ)*q g/(d:ℝ)|<t/(d:ℝ)):
    ((c:ℝ)*d)*(Fintype.card (retainedAndRawIntervalIndex π d σ false true r J w):ℝ)≤
      (n:ℝ)*((c:ℝ)*(q false+q true))+2*(c:ℝ)*t:=by
  have hdR:0<(d:ℝ):=by exact_mod_cast hd
  have hcR:0<(c:ℝ):=by exact_mod_cast hc
  have hroots:=retained_raw_interval_count_le_raw_counts π d σ false true r J w
  have h0:rawIntervalHubStartCount π d false σ w<(n:ℝ)*q false/(d:ℝ)+t/(d:ℝ):=by
    have hh:=(abs_lt.mp (hcounts false)).2
    linarith
  have h1:rawIntervalHubStartCount π d true σ w<(n:ℝ)*q true/(d:ℝ)+t/(d:ℝ):=by
    have hh:=(abs_lt.mp (hcounts true)).2
    linarith
  have hsum:(Fintype.card (retainedAndRawIntervalIndex π d σ false true r J w):ℝ)≤
      ((n:ℝ)*(q false+q true)+2*t)/(d:ℝ):=by
    have heq:((n:ℝ)*(q false+q true)+2*t)/(d:ℝ)=
      (n:ℝ)*q false/(d:ℝ)+(n:ℝ)*q true/(d:ℝ)+2*t/(d:ℝ):=by ring
    rw [heq,show 2*t/(d:ℝ)=2*(t/(d:ℝ)) by ring]
    linarith
  have hmul:((c:ℝ)*d)*(Fintype.card (retainedAndRawIntervalIndex π d σ false true r J w):ℝ)≤
      ((c:ℝ)*d)*(((n:ℝ)*(q false+q true)+2*t)/(d:ℝ)):=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  have heq:((c:ℝ)*d)*(((n:ℝ)*(q false+q true)+2*t)/(d:ℝ))=(n:ℝ)*((c:ℝ)*(q false+q true))+2*(c:ℝ)*t:=by
    field_simp
  exact heq ▸ hmul
end Oberwolfach
