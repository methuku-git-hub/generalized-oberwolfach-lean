module

public import Oberwolfach.FixedWeightOrderBounds

@[expose] public section

/-! Quantitative margins for active configuration counts. Removal bounds
are absolute cardinalities/degrees relative to the original order. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_active_cycle_margin (m:ℕ) (n a t δ β:ℝ)
    (hn:0≤n) (ha:0≤a) (han:a≤n) (ht:0≤t) (hd:0≤δ) (hb:0≤β)
    (hbudget:2*((m:ℝ)+1)*t+3*((m:ℝ)+1)*δ≤12*β*n):
    4*β*a^(m+1)+2*((m:ℝ)+1)*t*n^m+3*((m:ℝ)+1)*δ*a^m≤16*β*n^(m+1):=by
  have hp:=pow_le_pow_left₀ ha han m
  have hq:=pow_le_pow_left₀ ha han (m+1)
  have h0:=mul_le_mul_of_nonneg_left hq (by positivity:0≤4*β)
  have h1:=mul_le_mul_of_nonneg_left hp (by positivity:0≤3*((m:ℝ)+1)*δ)
  have h2:=mul_le_mul_of_nonneg_right hbudget (pow_nonneg hn m)
  simp only [pow_succ] at h0 ⊢
  nlinarith only [h0,h1,h2]

theorem marked_active_path_margin (m:ℕ) (hm:1≤m) (n a t δ β:ℝ)
    (hn:0≤n) (ha:0≤a) (han:a≤n) (ht:0≤t) (hd:0≤δ) (hb:0≤β)
    (hbudget:2*(m:ℝ)*t+4*((m:ℝ)+1)*δ≤12*β*n):
    4*β*a^m+2*(m:ℝ)*t*n^(m-1)+4*((m:ℝ)+1)*δ*a^(m-1)≤16*β*n^m:=by
  have hp:=pow_le_pow_left₀ ha han (m-1)
  have hq:=pow_le_pow_left₀ ha han m
  have h0:=mul_le_mul_of_nonneg_left hq (by positivity:0≤4*β)
  have h1:=mul_le_mul_of_nonneg_left hp (by positivity:0≤4*((m:ℝ)+1)*δ)
  have h2:=mul_le_mul_of_nonneg_right hbudget (pow_nonneg hn (m-1))
  have he:n^m=n*n^(m-1):=by rw [←pow_succ'];congr 1;omega
  rw [he] at h0 ⊢
  nlinarith only [h0,h1,h2]

theorem marked_active_cut_parameters (δ:ℝ) (hδ:0<δ) (hδ1:δ<1):
    0<1-δ/2∧0<δ/2∧1-2*δ≤(1-δ/2)*(1-2*(δ/2)):=by
  constructor
  · linarith
  constructor
  · positivity
  · nlinarith [sq_nonneg δ]

end Oberwolfach
