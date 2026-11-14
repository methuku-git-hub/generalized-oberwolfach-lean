module

public import Oberwolfach.OrdinaryPairCapacityRateChoices

@[expose] public section
/-! The post-spacing rates can also meet the sparse bad-graph load budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_pair_capacity_and_load_rate_choices
    (θ δ:ℝ) (hθ:0<θ) (hδ:0<δ):
    ∃D:ℕ,∀d:ℕ,D≤d→0<d ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧
      ∀a:ℝ,0<a→∃κ b:ℝ,0<κ ∧ 0<b ∧ b≤a/16 ∧ b≤δ/4 ∧
        16/(d:ℝ)+16*κ+16*b/a≤θ/8:=by
  obtain ⟨D,hD⟩:=ordinary_pair_and_residual_capacity_rate_choices θ hθ
  refine ⟨D,?_⟩
  intro d hd
  obtain ⟨hd0,hspace,hrates⟩:=hD d hd
  refine ⟨hd0,hspace,?_⟩
  intro a ha
  obtain ⟨κ,b₀,z,hκ,hb₀,hz,hbcap,hbudget⟩:=hrates a ha
  let b:=min b₀ (δ/8)
  have hb:0<b:=lt_min hb₀ (by positivity)
  have hb0:b≤b₀:=min_le_left _ _
  have hbδ:b≤δ/4:=by
    have hh:b≤δ/8:=min_le_right _ _
    linarith
  have hbdiv:b/a≤b₀/a:=div_le_div_of_nonneg_right hb0 ha.le
  have hbdiv':16*b/a≤16*b₀/a:=by
    convert mul_le_mul_of_nonneg_left hbdiv (show (0:ℝ)≤16 by norm_num) using 1 <;> ring
  exact ⟨κ,b,hκ,hb,hb0.trans hbcap,hbδ,by linarith⟩
end Oberwolfach
