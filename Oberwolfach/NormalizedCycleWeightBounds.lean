module

public import Oberwolfach.NormalizedWeightBounds

@[expose] public section
/-! Explicit two-sided bounds after normalization of fixed cycle weights. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem normalized_cycle_weight_bounds (r:ℕ) (hr:2≤r) (n D c cmin a b w:ℝ)
    (hn:0<n) (hDlo:n/2≤D) (hDhi:D≤2*n)
    (hcmin:0<cmin) (hclo:cmin≤c) (hchi:c≤1)
    (ha:0≤a) (hb:0≤b) (hwlo:a/n^(r-2)≤w) (hwhi:w≤b/n^(r-2)):
    a/n^(r-1)≤w/(D/2)/c ∧ w/(D/2)/c≤(4*b/cmin)/n^(r-1) := by
  have hpow:0<n^(r-2):=pow_pos hn _
  have hdlo:n/4≤D/2:=by linarith
  have hdhi:D/2≤n:=by linarith
  have hh:=normalized_weight_bounds n (n^(r-2)) (D/2) c cmin a b w hn hpow hdlo hdhi hcmin hclo hchi ha hb hwlo hwhi
  have hp:n^(r-2)*n=n^(r-1):=by
    have he:r-1=(r-2)+1:=by omega
    rw [he,pow_succ]
  simpa only [hp] using hh
end Oberwolfach
