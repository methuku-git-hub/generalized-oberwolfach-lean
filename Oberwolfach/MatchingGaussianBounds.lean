module

public import Oberwolfach.MatchingProbabilityBounds

@[expose] public section

/-! Gaussian estimates on the fixed, original test functions and degrees. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Oberwolfach

theorem matching_root_exponent {η D P K k n h v : ℝ}
    (hη : 0<η) (hD : 0<D) (hP : 0<P) (hK : 0<K) (hk : 1<k)
    (hn : 0<n) (hh : 0≤h) (hv : 0<v) (hvD : v≤D) (hscale : h*P^2≤n) :
    -2*(η*D/P)^2/((K*D/n)*(k-1)*v)≤-(2*η^2/(K*k))*h := by
  have hden : 0<(K*D/n)*(k-1)*v := by positivity
  have hlarge : 0<K*k*D^2/n := by positivity
  have hvar : (K*D/n)*(k-1)*v≤K*k*D^2/n := by
    have h1 := mul_le_mul_of_nonneg_left hvD (show 0≤(K*D/n)*(k-1) by positivity)
    have h2 := mul_le_mul_of_nonneg_left (show k-1≤k by linarith) (show 0≤K*D^2/n by positivity)
    calc
      _ ≤ (K*D/n)*(k-1)*D := h1
      _ = (K*D^2/n)*(k-1) := by ring
      _ ≤ (K*D^2/n)*k := h2
      _ = _ := by ring
  calc
    _ ≤ -2*(η*D/P)^2/(K*k*D^2/n) :=
      by
        have he := neg_le_neg (div_le_div_of_nonneg_left (show 0≤2*(η*D/P)^2 by positivity) hden hvar)
        simpa only [neg_mul,neg_div] using he
    _ = -(2*η^2/(K*k))*(n/P^2) := by field_simp <;> ring
    _ ≤ _ := mul_le_mul_of_nonpos_left ((le_div_iff₀ (sq_pos_of_pos hP)).mpr hscale) (neg_nonpos.mpr (by positivity))

theorem matching_vertex_weight_exponent {η W P b D k a n h : ℝ}
    (hη : 0<η) (hW : 0<W) (hP : 0<P) (hb : 0<b) (hD : 0<D)
    (hk : 0<k) (ha : 0<a) (hh : 0≤h) (hscale : h*P^2≤n) (hweight : a*b*D*n≤W) :
    -2*(η*W/P)^2/(b*D*k*W)≤-(2*η^2*a/k)*h := by
  have hp2 : 0<P^2 := sq_pos_of_pos hP
  have hratio : a*h≤W/(b*D*P^2) := by
    apply (le_div_iff₀ (by positivity : 0<b*D*P^2)).mpr
    have he := mul_le_mul_of_nonneg_left hscale (show 0≤a*b*D by positivity)
    nlinarith
  calc
    _ = -(2*η^2/k)*(W/(b*D*P^2)) := by field_simp <;> ring
    _ ≤ -(2*η^2/k)*(a*h) := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr (by positivity))
    _ = _ := by ring

theorem matching_selected_weight_exponent {η W D P p q h : ℝ}
    (hη : 0<η) (hW : 0<W) (hD : 0<D) (hP : 0<P) (hp : 0<p) (hq : 0<q)
    (hh : 0≤h) (hscale : D^2*p*h≤4*P^2*q^2) :
    -2*(η*W/D)^2/(p*(2*W/(P*q))^2)≤-(η^2/8)*h := by
  have hratio : h/4≤P^2*q^2/(D^2*p) := by
    apply (le_div_iff₀ (by positivity : 0<D^2*p)).mpr
    nlinarith
  calc
    _ = -(η^2/2)*(P^2*q^2/(D^2*p)) := by field_simp <;> ring
    _ ≤ -(η^2/2)*(h/4) := mul_le_mul_of_nonpos_left hratio (neg_nonpos.mpr (by positivity))
    _ = _ := by ring

theorem matching_edge_weight_exponent {η W P q b D a n h : ℝ}
    (hη : 0≤η) (hη1 : η≤1/100) (hW : 0<W) (hP : 0<P) (hq : 0<q)
    (hb : 0<b) (hD : 0<D) (ha : 0<a) (hh : 0≤h)
    (hscale : h*P*q≤D*n) (hweight : a*b*D*n≤W) :
    (((W/P+η*W/P)/q*(Real.exp (1/4)-1)-(1/4)*(2*W/(P*q)))/b)≤-(a/8)*h := by
  have he := matching_weight_exponent hη hη1 (z:=W/(P*q)) (by positivity) hb
    (μ:=(W/P+η*W/P)/q) (by apply le_of_eq;field_simp <;> ring)
  have hz : a*h≤W/(P*q*b) := by
    apply (le_div_iff₀ (by positivity : 0<P*q*b)).mpr
    have hm := mul_le_mul_of_nonneg_left hscale (show 0≤a*b by positivity)
    nlinarith
  calc
    _ = (((W/P+η*W/P)/q*(Real.exp (1/4)-1)-(1/4)*(2*(W/(P*q))))/b) := by ring
    _ ≤ -(W/(P*q))/(8*b) := he
    _ = -(1/8)*(W/(P*q*b)) := by ring
    _ ≤ -(1/8)*(a*h) := mul_le_mul_of_nonpos_left hz (by norm_num)
    _ = _ := by ring

end Oberwolfach
