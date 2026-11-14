module

public import Oberwolfach.ResidualActualVertexCard

@[expose] public section
/-! Numerical comparison with the remainder obtained by selecting every
segment. This isolates the arithmetic from the geometric deletion proof. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem residual_full_selection_comparison_arithmetic
    (R Rfull n C p q m h missing c d:ℕ) (hc:1≤c)
    (hR:R+C+p+c*q=n+h) (hfull:Rfull+C+p+c*(d*m)=n+m)
    (hq:q+missing=d*m) (hupper:h≤m+missing) (hlower:m≤h+missing):
    Rfull≤R ∧ R≤Rfull+(c+1)*missing := by
  have hcpos:0≤(c-1)*missing:=Nat.zero_le _
  have heq:c*q+c*missing=c*(d*m):=by rw [←Nat.mul_add,hq]
  have hone:missing≤c*missing:=by nlinarith
  constructor <;> nlinarith
end Oberwolfach
