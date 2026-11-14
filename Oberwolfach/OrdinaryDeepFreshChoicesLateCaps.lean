module

public import Oberwolfach.OrdinaryDeepParentFreshProbabilityChoices
public import Oberwolfach.OrdinaryDeepParentNumericScale

@[expose] public section
/-! Retain the exact factor probability tolerances and choose all four
    later parent errors below any subsequently supplied positive cap. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_deep_fresh_choices_late_caps
    (pmin κe a K bcap Bmin:ℝ) (hp:0<pmin) (hκe:0<κe) (ha:0<a) (hK:0<K)
    (hbcap:0<bcap) (hBmin:0≤Bmin):
    ∃γ κ b B εf ηf ζ:ℝ,
      0<γ ∧ 0<κ ∧ 0<b ∧ b≤bcap ∧ 0<B ∧ Bmin≤B ∧
      0<εf ∧ 0<ηf ∧ 0<ζ ∧
      OrdinaryTriangleFreshFactorProbabilityProperty γ κ b B εf ηf ζ ∧
    ∀cap:ℝ,0<cap→∃δ ε t lam:ℝ,δ≤cap ∧ ε≤cap ∧ t≤cap ∧ lam≤cap ∧
      OrdinaryDeepNumericParameters pmin κe a ηf εf K γ κ δ ε t lam b B :=by
  obtain ⟨γ,κ,b,B,εf,ηf,ζ,δ,ε,t,lam,hγ,hκ,hb,hbcap',hB,hBmin',hεf,hηf,hζ,hnum,hprob⟩:=
    ordinary_deep_parent_fresh_probability_choices pmin κe a K bcap Bmin hp hκe ha hK hbcap hBmin
  refine ⟨γ,κ,b,B,εf,ηf,ζ,hγ,hκ,hb,hbcap',hB,hBmin',hεf,hηf,hζ,hprob,?_⟩
  intro cap hcap
  exact ordinary_deep_parent_numeric_cap pmin κe a ηf εf K γ κ δ ε t lam b B cap hηf.le hcap hnum
end Oberwolfach
