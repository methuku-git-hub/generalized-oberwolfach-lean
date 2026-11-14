module

public import Oberwolfach.AsymptoticMargins
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section

/-! Choose the bounded set size from the degree margin before the conflict
degree bound, and only then choose the ambient order. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace Oberwolfach

theorem rooted_conflict_loss_le (n s k : ℕ) (hn : 0<n) (hns : 2*s≤n)
    (L : ℝ) (hL : 0≤L) :
    let q : ℝ := (k:ℝ)/(n-s:ℕ)
    L*(2*(s:ℝ)*q+n*q^2)≤L*(4*s*k+4*(k:ℝ)^2)/n := by
  intro q
  have hs : s≤n := by omega
  have hden : (0:ℝ)<(n-s:ℕ) := by exact_mod_cast (show 0<n-s by omega)
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have hbase : (n:ℝ)≤2*(n-s:ℕ) := by exact_mod_cast (show n≤2*(n-s) by omega)
  have hq : q≤2*k/(n:ℝ) := by
    apply (div_le_div_iff₀ hden hnr).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hbase (Nat.cast_nonneg (α:=ℝ) k)]
  have hq0 : 0≤q := by dsimp [q];positivity
  have hsq : q^2≤(2*k/(n:ℝ))^2 := (sq_le_sq₀ hq0 (by positivity)).mpr hq
  have hlin := mul_le_mul_of_nonneg_left hq (show (0:ℝ)≤2*s by positivity)
  have hquad := mul_le_mul_of_nonneg_left hsq hnr.le
  calc
    _ ≤ L*(2*(s:ℝ)*(2*k/n)+(n:ℝ)*(2*k/n)^2) :=
      mul_le_mul_of_nonneg_left (add_le_add hlin hquad) hL
    _ = _ := by field_simp;ring


theorem rooted_dense_set_scales (s : ℕ) (α : ℝ) (hα : 0<α) :
    ∃ K : ℕ,∀ k : ℕ,K≤k → 2≤k ∧
      (s:ℝ)+1≤α*(s+k:ℝ)/4 ∧
      2*(s+k:ℝ)*Real.exp (-α^2*(s+k:ℝ)/8)≤1/4 ∧
      ∀ L : ℝ,0≤L → ∃ N : ℕ,∀ n : ℕ,N≤n → 0<n ∧ 2*(s+k)≤n ∧
        L*(2*(s:ℝ)*((k:ℝ)/(n-s:ℕ))+n*((k:ℝ)/(n-s:ℕ))^2)≤1/4 := by
  obtain ⟨K₁,h₁⟩ := eventually_stretchedExp_le_inv_pow 8 1
    (c:=α^2/8) (p:=1) (by positivity) (by norm_num) 0
  obtain ⟨K₂,h₂⟩ := eventually_constant_le_linear ((s:ℝ)+1) (α/4) (by positivity)
  refine ⟨max (max K₁ K₂) 2,?_⟩
  intro k hk
  have ha := h₂ k (by omega)
  have hb := h₁ (s+k) (by omega)
  simp only [Real.rpow_one,pow_zero,div_one,Nat.cast_add] at hb
  have hroot : (s:ℝ)+1≤α*(s+k:ℝ)/4 := by
    have hh := mul_nonneg hα.le (Nat.cast_nonneg (α:=ℝ) s)
    nlinarith only [ha,hh]
  refine ⟨by omega,hroot,?_,?_⟩
  · have he : -(α^2/8)*(s+k:ℝ) = -α^2*(s+k:ℝ)/8 := by ring
    rw [he] at hb
    linarith only [hb]
  · intro L hL
    obtain ⟨N₁,hN₁⟩ := eventually_constant_le_linear (4*L*(4*s*k+4*(k:ℝ)^2)) 1 (by norm_num)
    refine ⟨max N₁ (2*(s+k)+1),?_⟩
    intro n hn
    have hnp : 0<n := by omega
    have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hnp
    have hb := hN₁ n (by omega)
    simp only [one_mul] at hb
    refine ⟨hnp,by omega,(rooted_conflict_loss_le n s k hnp (by omega) L hL).trans ?_⟩
    apply (div_le_iff₀ hnr).mpr
    linarith only [hb]

end Oberwolfach
