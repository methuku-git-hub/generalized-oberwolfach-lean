module

public import Oberwolfach.FiniteInverseCubeTail
public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! Uniform error budget for distinct local scales, independent of their number. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem local_row_distinct_scales_error_budget (C δ:ℝ) (hC:0≤C) (hδ:0<δ) :
    ∃m:ℕ,1≤m ∧ ∀(I:Type) (T:Finset I) (a b:I→ℕ),
      (∀i∈T,m≤a i) → Set.InjOn a T →
      (∀i∈T,(b i:ℝ)≤C*(a i:ℝ)) →
      (∑i∈T,2*(b i:ℝ)*Real.exp (-2*(a i:ℝ)^(1/2:ℝ)))≤δ := by
  obtain ⟨N,hN⟩:=eventually_stretchedExp_le_inv_pow (2*C) 1 (c:=2) (p:=1/2) (by norm_num) (by norm_num) 3
  obtain ⟨M,hM⟩:=exists_nat_gt (8/δ)
  let m:=max (max N M) 1
  refine ⟨m,by dsimp [m];omega,?_⟩
  intro I T a b hmin hinj hB
  have hm1:1≤m:=by dsimp [m];omega
  have hmpos:(0:ℝ)<m:=by exact_mod_cast (show 0<m by omega)
  have hNle:N≤m:=by dsimp [m];omega
  have hMle:M≤m:=by dsimp [m];omega
  have hSmall : 8/(m:ℝ)≤δ := by
    have hgt:(8/δ:ℝ)<m:=lt_of_lt_of_le hM (by exact_mod_cast hMle)
    have hh:(8:ℝ)<(m:ℝ)*δ:=(div_lt_iff₀ hδ).1 hgt
    apply (div_le_iff₀ hmpos).2
    linarith
  have hterm : ∀i∈T,2*(b i:ℝ)*Real.exp (-2*(a i:ℝ)^(1/2:ℝ))≤1/(a i:ℝ)^3 := by
    intro i hi
    have ha:=hN (a i) (le_trans hNle (hmin i hi))
    simp only [Real.rpow_one] at ha
    have hp:0≤Real.exp (-2*(a i:ℝ)^(1/2:ℝ)):=(Real.exp_pos _).le
    have hh:=mul_le_mul_of_nonneg_right (hB i hi) (by positivity : 0≤2*Real.exp (-2*(a i:ℝ)^(1/2:ℝ)))
    nlinarith only [hh,ha]
  have hImage : ∀k∈T.image a,m≤k := by
    intro k hk
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp hk
    exact hmin i hi
  have htail:=inverse_cube_finset_tail_bound (T.image a) m hm1 hImage
  have hsum : (∑i∈T,(1:ℝ)/(a i:ℝ)^3)≤8/(m:ℝ) := by
    have hEq : (∑k∈T.image a,(1:ℝ)/(k:ℝ)^3) = ∑i∈T,(1:ℝ)/(a i:ℝ)^3 :=
      Finset.sum_image (f:=fun k:ℕ=>(1:ℝ)/(k:ℝ)^3) hinj
    rw [hEq] at htail
    exact htail
  exact (Finset.sum_le_sum hterm).trans (hsum.trans hSmall)
end Oberwolfach
