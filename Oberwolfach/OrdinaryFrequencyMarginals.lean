module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! The ordinary-class retained frequencies give the actual marked,
ordinary and unassigned index-state marginals. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_frequency_marginal_bounds
    (s θ c long short omitted:ℝ)
    (hs0:0≤s) (hs1:s≤1/100) (hθ0:0≤θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hlong:0≤long) (hshort:0≤short) (homit:0≤omitted) (homitmax:omitted≤θ/50)
    (hfreq:long+short+omitted=1-s):
    let a:=(1-θ)*long/c
    let b:=(c-1)*a+(1-θ)*short
    let u:=1-s-a-b;
    u=θ*(1-s)+(1-θ)*omitted ∧ θ/2≤u ∧ u≤2*θ ∧
    0≤a ∧ a≤1/c ∧ 1/2≤b ∧ s+a+b+u=1 := by
  intro a b u
  have hc0:0<c:=by linarith
  have hθc:0≤1-θ:=by linarith
  have hlong1:long≤1:=by linarith
  have hlongprod:0≤θ*long:=mul_nonneg hθ0 hlong
  have homitprod:0≤θ*omitted:=mul_nonneg hθ0 homit
  have hsprod:0≤θ*s:=mul_nonneg hθ0 hs0
  have hθsbound:0≤θ*(1/100-s):=mul_nonneg hθ0 (by linarith)
  have ha:0≤a:=by dsimp [a];positivity
  have ha1:a≤1/c:=by
    dsimp [a]
    apply (div_le_div_iff_of_pos_right hc0).2
    nlinarith
  have hca:c*a=(1-θ)*long:=by dsimp [a];field_simp
  have hu:u=θ*(1-s)+(1-θ)*omitted:=by dsimp [u,b];nlinarith
  have huLo:θ/2≤u:=by rw [hu];nlinarith
  have huHi:u≤2*θ:=by rw [hu];nlinarith
  have ha8:a≤1/8:=by
    have hh:1/c≤(1/8:ℝ):=by apply (div_le_div_iff₀ hc0 (by norm_num)).2;nlinarith
    exact ha1.trans hh
  have hb:1/2≤b:=by dsimp [u] at huHi;nlinarith
  refine ⟨hu,huLo,huHi,ha,ha1,hb,?_⟩
  dsimp [u];ring
end Oberwolfach
