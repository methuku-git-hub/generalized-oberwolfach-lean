module

public import Oberwolfach.UniformStartRetentionMinimum
public import Oberwolfach.AsymptoticMargins

@[expose] public section

/-! Quantitative conversion of the raw start-count error n^(3/5) to the
conditional deletion bound (4d/p)n^(-2/5). The order is uniform in the raw sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Filter
noncomputable section
namespace Oberwolfach

theorem retention_error_div_order (n : ℝ) (hn : 0<n) :
    n^(3/5:ℝ)/n=n^(-2/5:ℝ) := by
  rw [← Real.rpow_sub_one hn.ne']
  norm_num

theorem eventually_retention_error_small (p : ℝ) (hp : 0<p) (d : ℕ) (hd : 0<d) :
    ∃ N : ℕ,1≤N ∧ ∀ n : ℕ,N≤n → (n:ℝ)^(3/5:ℝ)≤p*n/(2*d) := by
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hh := (tendsto_rpow_neg_atTop (y:=(2/5:ℝ)) (by norm_num)).comp tendsto_natCast_atTop_atTop
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hh.eventually (eventually_lt_nhds (by positivity : (0:ℝ)<p/(2*d))))
  refine ⟨max N 1,le_max_right _ _,?_⟩
  intro n hn
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hsmall : (n:ℝ)^(-2/5:ℝ)≤p/(2*d) := by
    simpa only [Function.comp_apply,neg_div] using (hN n (by omega)).le
  have hscale := retention_error_div_order (n:ℝ) hnR
  rw [← hscale] at hsmall
  have hb := (div_le_iff₀ hnR).mp hsmall
  convert hb using 1 <;> ring

theorem startRetentionMinimum_polynomial_rate
    {V U : Type} [Fintype V] [Fintype U] [Nonempty V] [DecidableEq V] [DecidableEq U]
    (A : V→Finset U) (n d : ℕ) (hn : 0<n) (hd : 0<d) (p μ : ℝ) (hp : 0<p)
    (hμ : p*n/d≤μ) (hsmall : (n:ℝ)^(3/5:ℝ)≤p*n/(2*d))
    (hcounts : ∀ a,|((A a).card:ℝ)-μ|≤(n:ℝ)^(3/5:ℝ)) (a : V) :
    (((A a).card-startRetentionMinimum A:ℕ):ℝ)/(A a).card≤(4*d/p)*(n:ℝ)^(-2/5:ℝ) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hdR : (0:ℝ)<d := by exact_mod_cast hd
  have hμpos : 0<μ := lt_of_lt_of_le (by positivity) hμ
  have hsmall' : (n:ℝ)^(3/5:ℝ)≤μ/2 := by
    have he : p*n/(2*d)=(p*n/d)/2 := by ring
    rw [he] at hsmall
    linarith
  have hh := startRetentionMinimum_deletion_fraction A μ ((n:ℝ)^(3/5:ℝ)) hμpos (by positivity) hsmall' hcounts a
  apply hh.trans
  calc
    _ ≤ (4*(n:ℝ)^(3/5:ℝ))/(p*n/d) := div_le_div_of_nonneg_left (by positivity) (by positivity) hμ
    _ = (4*d/p)*((n:ℝ)^(3/5:ℝ)/n) := by field_simp <;> ring
    _ = _ := by rw [retention_error_div_order (n:ℝ) hnR]

theorem retention_raw_failure_order (n m : ℕ) (hn : 0<n) (hm : 0<m) (hmn : m≤n) :
    2*n*Real.exp (-2*((n:ℝ)^(3/5:ℝ))^2/m)≤2*n*Real.exp (-2*(n:ℝ)^(1/5:ℝ)) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have hmR : (0:ℝ)<m := by exact_mod_cast hm
  have he : ((n:ℝ)^(3/5:ℝ))^2/n=(n:ℝ)^(1/5:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hnR.le,← Real.rpow_sub_one hnR.ne']
    norm_num
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hb : ((n:ℝ)^(3/5:ℝ))^2/n≤((n:ℝ)^(3/5:ℝ))^2/m :=
    div_le_div_of_nonneg_left (sq_nonneg ((n:ℝ)^(3/5:ℝ))) hmR (by exact_mod_cast hmn)
  rw [he] at hb
  rw [mul_div_assoc]
  linarith only [hb]

end Oberwolfach
