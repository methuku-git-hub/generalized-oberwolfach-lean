module

public import Oberwolfach.EndpointMatchingMass

@[expose] public section

/-! The fixed density normalization of endpoint triangles: original row
scale a, original index scale b, two rim factors and three spoke factors. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach

theorem endpoint_triangle_coefficient_bounds (a b κ p q s c C w : ℝ)
    (ha : 0<a) (hκ : 0<κ) (hp : 0<p) (hc : 0≤c) (hC : 0≤C)
    (hb : κ*a≤b) (hba : b≤a) (hq : p≤q) (hq1 : q≤1) (hs : p≤s) (hs1 : s≤1)
    (hw : c/a≤w ∧ w≤C/a) :
    c/a^2≤w/(b*q^2*s^3) ∧ w/(b*q^2*s^3)≤(C/(κ*p^5))/a^2 := by
  have hbpos : 0<b := (mul_pos hκ ha).trans_le hb
  have hqpos : 0<q := hp.trans_le hq
  have hspos : 0<s := hp.trans_le hs
  have hdpos : 0<b*q^2*s^3 := by positivity
  have hupper : b*q^2*s^3≤a := by
    have h1:=mul_le_mul_of_nonneg_left (pow_le_one₀ hqpos.le hq1 (n:=2)) hbpos.le
    have h2:=mul_le_mul_of_nonneg_left (pow_le_one₀ hspos.le hs1 (n:=3)) (by positivity : 0≤b*q^2)
    nlinarith only [h1,h2,hba]
  have hlower : κ*p^5*a≤b*q^2*s^3 := by
    have h1:=mul_le_mul hb (pow_le_pow_left₀ hp.le hq 2) (by positivity : 0≤p^2) hbpos.le
    have h2:=mul_le_mul h1 (pow_le_pow_left₀ hp.le hs 3) (by positivity : 0≤p^3) (by positivity : 0≤b*q^2)
    convert h2 using 1 <;> ring
  constructor
  · calc
      _ = (c/a)/a := by ring
      _ ≤ (c/a)/(b*q^2*s^3) := div_le_div_of_nonneg_left (div_nonneg hc ha.le) hdpos hupper
      _ ≤ _ := div_le_div_of_nonneg_right hw.1 hdpos.le
  · calc
      _ ≤ (C/a)/(b*q^2*s^3) := div_le_div_of_nonneg_right hw.2 hdpos.le
      _ ≤ (C/a)/(κ*p^5*a) := div_le_div_of_nonneg_left (div_nonneg hC ha.le) (by positivity) hlower
      _ = _ := by ring

theorem endpoint_index_target_error (a b κ p q s C L m M δ : ℝ)
    (ha : 0<a) (hκ : 0<κ) (hp : 0<p) (hC : 0≤C) (hL : 0≤L)
    (hb : κ*a≤b) (hq : 0≤q) (hq1 : q≤1) (hs : p≤s)
    (hM : |M-m/2|≤(1+2*C)*L/2) (hbalance : |q*m/(2*b*s)-1|≤δ) :
    |q/(b*s)*M-1|≤δ+((1+2*C)/(2*κ*p))*L/a := by
  have hbpos : 0<b := (mul_pos hκ ha).trans_le hb
  have hspos : 0<s := hp.trans_le hs
  have hscale : q/(b*s)≤1/(κ*p*a) := by
    calc
      _ ≤ 1/(b*s) := div_le_div_of_nonneg_right hq1 (by positivity)
      _ ≤ 1/(κ*p*a) := by
        apply one_div_le_one_div_of_le (by positivity)
        have hh:=mul_le_mul hb hs hp.le hbpos.le
        nlinarith only [hh]
  have hmul:=mul_le_mul_of_nonneg_left hM (div_nonneg hq (by positivity : 0≤b*s))
  have hbound:=mul_le_mul_of_nonneg_right hscale (by positivity : 0≤(1+2*C)*L/2)
  have habs : |q/(b*s)*M-q*m/(2*b*s)|=q/(b*s)*|M-m/2| := by
    rw [show q/(b*s)*M-q*m/(2*b*s)=q/(b*s)*(M-m/2) by ring,abs_mul,
      abs_of_nonneg (div_nonneg hq (by positivity))]
  have htriangle:=abs_sub_le (q/(b*s)*M) (q*m/(2*b*s)) 1
  rw [habs] at htriangle
  have he : (1/(κ*p*a))*((1+2*C)*L/2)=((1+2*C)/(2*κ*p))*L/a := by ring
  rw [he] at hbound
  linarith only [htriangle,hmul,hbound,hbalance]

end Oberwolfach
