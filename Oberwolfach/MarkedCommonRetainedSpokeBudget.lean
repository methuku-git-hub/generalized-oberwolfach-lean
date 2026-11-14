module

public import Oberwolfach.LongMatchingCommonRetainedSpokeBounds

@[expose] public section
/-! A selector neighbourhood error below the retention rate supplies both
ambient retained-spoke loss bounds. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_common_retained_spoke_budget
    (h:ℕ) (εnbr ζret:ℝ) (hnbr:0≤εnbr) (hcap:εnbr≤ζret):
    ∀(n:ℕ) (U:Type) [Fintype U],Fintype.card U≤n→
      (εnbr/(2*((h:ℝ)+1)))*Fintype.card U≤ζret*n ∧
      (εnbr/(2*((h:ℝ)+1)))*n≤ζret*n :=by
  intro n U _ hu
  have hh:0≤(h:ℝ):=by positivity
  have hden:1≤2*((h:ℝ)+1):=by linarith
  have hfrac0:0≤εnbr/(2*((h:ℝ)+1)):=by positivity
  have hfrac:εnbr/(2*((h:ℝ)+1))≤ζret:=(div_le_self hnbr hden).trans hcap
  have hn:0≤(n:ℝ):=by positivity
  have hu':(Fintype.card U:ℝ)≤n:=by exact_mod_cast hu
  have h1:=mul_le_mul_of_nonneg_left hu' hfrac0
  have h2:=mul_le_mul_of_nonneg_right hfrac hn
  exact ⟨h1.trans h2,h2⟩
end Oberwolfach
