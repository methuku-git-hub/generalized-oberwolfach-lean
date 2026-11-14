module

public import Oberwolfach.ReservedCapacityFromReal
public import Oberwolfach.LongComponentCountEstimate
public import Mathlib.Tactic

@[expose] public section
/-! Reserved-path blocks suffice for any positive lower bound on the long
component fraction. This includes the smaller active ordinary-class bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_reserved_block_capacity
    {I:Type} [Fintype I] (a:I→ℕ) (t K demand:ℕ) (N ell ell0 θ err:ℝ)
    (ht:0<t) (hK:0<K) (hN:0≤N) (hθ:0<θ) (hell0:0<ell0) (hell:ell0≤ell)
    (hmin:∀i,K≤a i) (htotal:((∑i,a i:ℕ):ℝ)=ell*N)
    (hcut:5/((t:ℝ)+5)+(t:ℝ)/K≤θ/2)
    (herr:err<θ*ell0*N/(2*(t:ℝ)))
    (hdemand:(demand:ℝ)≤(1-θ)*ell*N/(t:ℝ)+err):
    demand≤∑i,a i/(t+5) :=by
  classical
  have htR:0<(t:ℝ):=by exact_mod_cast ht
  have hKR:0<(K:ℝ):=by exact_mod_cast hK
  have helln:0≤ell*N:=mul_nonneg (le_of_lt (lt_of_lt_of_le hell0 hell)) hN
  have hgap:θ/2≤θ-5/((t:ℝ)+5)-(t:ℝ)/K:=by linarith
  have hbase:ell0*N/(t:ℝ)≤ell*N/(t:ℝ):=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hell hN) htR.le
  have hprod:θ*ell0*N/(2*(t:ℝ))≤
      (ell*N/(t:ℝ))*(θ-5/((t:ℝ)+5)-(t:ℝ)/K):=by
    calc
      _ = (ell0*N/(t:ℝ))*(θ/2):=by ring
      _ ≤ (ell*N/(t:ℝ))*(θ/2):=mul_le_mul_of_nonneg_right hbase (by positivity)
      _ ≤ _ :=mul_le_mul_of_nonneg_left hgap (div_nonneg helln htR.le)
  have hid:ell*N/((t:ℝ)+5)-ell*N/K-(1-θ)*ell*N/(t:ℝ)=
      (ell*N/(t:ℝ))*(θ-5/((t:ℝ)+5)-(t:ℝ)/K):=by
    field_simp
    <;> ring
  have hsur:(demand:ℝ)<((∑i,a i:ℕ):ℝ)/(t+5:ℕ)-((∑i,a i:ℕ):ℝ)/(K:ℝ):=by
    rw [htotal]
    push_cast
    linarith
  have hcomponents:=component_count_le_total_div a K hK hmin
  exact sum_floor_capacity_of_real_surplus a (t+5) demand (((∑i,a i:ℕ):ℝ)/(K:ℝ)) (by omega) hcomponents hsur
end Oberwolfach
