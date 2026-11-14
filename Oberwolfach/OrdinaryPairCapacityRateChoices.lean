module

public import Oberwolfach.OrdinaryProtectedPairSpacing

@[expose] public section
/-! A single early choice of the spacing parameter leaves room both for
protected-pair labels and for the later residual-capacity budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_pair_and_residual_capacity_rate_choices
    (θ:ℝ) (hθ:0<θ):
    ∃D:ℕ,∀d:ℕ,D≤d→0<d ∧ 1/(4*(d:ℝ))≤5*θ^2/256 ∧
      ∀a:ℝ,0<a→∃κ b z:ℝ,0<κ ∧ 0<b ∧ 0<z ∧ b≤a/16 ∧
        16/(d:ℝ)+16*κ+16*b/a+4*z≤θ/8:=by
  obtain ⟨D₀,hD₀⟩:=ordinary_protected_pair_spacing_choice θ hθ
  obtain ⟨D₁,hD₁⟩:=exists_nat_gt (256/θ)
  refine ⟨max D₀ D₁,?_⟩
  intro d hd
  obtain ⟨hd0,hspace⟩:=hD₀ d (by omega)
  have hdR:0<(d:ℝ):=by exact_mod_cast hd0
  have hbound:256/θ≤(d:ℝ):=le_of_lt (lt_of_lt_of_le hD₁ (by exact_mod_cast (show D₁≤d by omega)))
  have hmul:256≤(d:ℝ)*θ:=(div_le_iff₀ hθ).1 hbound
  have hsmall:16/(d:ℝ)≤θ/16:=by
    apply (div_le_iff₀ hdR).2
    nlinarith
  refine ⟨hd0,hspace,?_⟩
  intro a ha
  let κ:=θ/2048
  let b:=a*min (1/32:ℝ) (θ/2048)
  let z:=θ/512
  have hm:0<min (1/32:ℝ) (θ/2048):=lt_min (by norm_num) (by positivity)
  have hb:0<b:=mul_pos ha hm
  have hb1:b≤a/16:=by
    dsimp [b]
    have hh:min (1/32:ℝ) (θ/2048)≤1/32:=min_le_left _ _
    nlinarith
  have hb2:b/a≤θ/2048:=by
    dsimp [b]
    rw [mul_div_cancel_left₀ _ (ne_of_gt ha)]
    exact min_le_right _ _
  have hb3:16*b/a≤16*(θ/2048):=by
    convert mul_le_mul_of_nonneg_left hb2 (show (0:ℝ)≤16 by norm_num) using 1 <;> ring
  refine ⟨κ,b,z,by dsimp [κ];positivity,hb,by dsimp [z];positivity,hb1,?_⟩
  dsimp [κ,z]
  nlinarith
end Oberwolfach
