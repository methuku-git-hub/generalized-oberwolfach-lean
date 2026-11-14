module

public import Oberwolfach.OrdinaryCycleSampleExpectations

@[expose] public section
/-! A fixed linear sampling scale for bounded ordinary-cycle weights. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_cycle_sampling_scaled_probability {V:Type} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (hr:3≤r) (hn:0<Fintype.card V) (B:ℝ) (hB:0<B)
    (w:OrdinaryCycle G r→ℝ)
    (hw:∀ C,0≤w C ∧ w C≤B/(Fintype.card V:ℝ)^(r-2)):
    ∀ C,0≤((Fintype.card V:ℝ)/(2*B))*w C ∧ ((Fintype.card V:ℝ)/(2*B))*w C≤1/2 := by
  intro C
  have hn1:(1:ℝ)≤Fintype.card V:=by exact_mod_cast hn
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hpow:(Fintype.card V:ℝ)≤(Fintype.card V:ℝ)^(r-2):=by
    calc
      _ = (Fintype.card V:ℝ)^1:=by simp
      _ ≤ (Fintype.card V:ℝ)^(r-2):=pow_le_pow_right₀ hn1 (by omega)
  have hp:0<(Fintype.card V:ℝ)^(r-2):=pow_pos hnpos _
  have htotal:w C*(Fintype.card V:ℝ)^(r-2)≤B:=(le_div_iff₀ hp).mp (hw C).2
  have hh:=mul_le_mul_of_nonneg_right hpow (hw C).1
  have hnum:(Fintype.card V:ℝ)*w C≤B:=by nlinarith
  have hden:0<2*B:=by positivity
  have hratio:((Fintype.card V:ℝ)*w C)/(2*B)≤1/2:=
    (div_le_iff₀ hden).2 (by nlinarith)
  constructor
  · exact mul_nonneg (div_nonneg hnpos.le hden.le) (hw C).1
  · convert hratio using 1 <;> ring

theorem ordinary_cycle_sampling_vertex_mean_lower
    (n degree B:ℝ) (hn:0≤n) (hB:0<B) (hdeg:n/2≤degree):
    n^2/(8*B)≤(n/(2*B))*degree/2 := by
  have hh:=mul_le_mul_of_nonneg_left hdeg (div_nonneg hn (by positivity:0≤2*B))
  have hpos:0<8*B:=by positivity
  have heq:(n/(2*B))*(n/2)/2=n^2/(8*B):=by field_simp;ring
  rw [←heq]
  linarith only [hh]

theorem ordinary_cycle_sampling_pair_mean_scale
    (n B r:ℝ) (hB:0<B):
    (n/(2*B))*(r^2*B)=r^2*n/2 := by field_simp
end Oberwolfach
