module

public import Oberwolfach.OrdinaryPositionCapacityArithmetic

@[expose] public section
/-! Convert the edge-count bound and the assignment ceiling into the
normalised matching-size bound used in the capacity calculation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_assigned_ceiling_bound
    (n θ C ε lam a d E:ℝ) (hn:0<n) (ha:0<a) (hE0:0≤E)
    (hE:E≤C*(θ*ε^2+lam*ε)*n^2+C*d*n):
    ((⌈4*E/(a*n)⌉₊:ℕ):ℝ) ≤
      4*C*(θ*ε^2+lam*ε)*(1/a)*n+(4*C*d/a+1) := by
  have hquot:0≤4*E/(a*n):=by positivity
  have hceil:((⌈4*E/(a*n)⌉₊:ℕ):ℝ)≤4*E/(a*n)+1 := (Nat.ceil_lt_add_one hquot).le
  have hbound:=mul_le_mul_of_nonneg_left hE (show 0≤4/(a*n) by positivity)
  have hnorm:(4/(a*n))*(C*(θ*ε^2+lam*ε)*n^2+C*d*n)=
      4*C*(θ*ε^2+lam*ε)*(1/a)*n+4*C*d/a := by field_simp <;> ring
  have hleft:(4/(a*n))*E=4*E/(a*n):=by ring
  rw [hnorm,hleft] at hbound
  linarith
end Oberwolfach
