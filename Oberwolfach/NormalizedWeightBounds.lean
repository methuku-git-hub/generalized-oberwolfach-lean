module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! Bounds for the fixed cycle coefficients after degree and density normalization. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
theorem normalized_weight_bounds (n S d c cmin a b w:ℝ)
    (hn:0<n) (hS:0<S) (hdlo:n/4≤d) (hdhi:d≤n)
    (hcmin:0<cmin) (hclo:cmin≤c) (hchi:c≤1)
    (ha:0≤a) (hb:0≤b) (hwlo:a/S≤w) (hwhi:w≤b/S):
    a/(S*n)≤w/d/c ∧ w/d/c≤(4*b/cmin)/(S*n) := by
  have hd:0<d:=by linarith
  have hc:0<c:=lt_of_lt_of_le hcmin hclo
  have hA:0≤a/S:=div_nonneg ha hS.le
  have hB:0≤b/S:=div_nonneg hb hS.le
  have hLow1:a/S/n≤a/S/d:=div_le_div_of_nonneg_left hA hd hdhi
  have hLow2:a/S/d≤(a/S/d)/c:=by
    have hh:=div_le_div_of_nonneg_left (div_nonneg hA hd.le) hc hchi
    simpa only [div_one] using hh
  have hLow3:(a/S/d)/c≤w/d/c:=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hwlo hd.le) hc.le
  have hlow:a/(S*n)≤w/d/c:=by
    rw [←div_div]
    exact hLow1.trans (hLow2.trans hLow3)
  have hUp1:w/d/c≤(b/S/d)/c:=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hwhi hd.le) hc.le
  have hn4:0<n/4:=by positivity
  have hUp2:(b/S/d)/c≤(b/S/(n/4))/c:=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_left hB hn4 hdlo) hc.le
  have hUp3:(b/S/(n/4))/c≤(b/S/(n/4))/cmin:=
    div_le_div_of_nonneg_left (div_nonneg hB hn4.le) hcmin hclo
  have hEq:(b/S/(n/4))/cmin=(4*b/cmin)/(S*n):=by
    field_simp
    <;> ring
  exact ⟨hlow,by rw [←hEq];exact hUp1.trans (hUp2.trans hUp3)⟩
end Oberwolfach
