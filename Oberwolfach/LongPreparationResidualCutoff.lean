module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

@[expose] public section
/-! A finite cutoff chosen before the graph order supplies the residual
interval margin for any fixed positive remainder parameter. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_preparation_residual_cutoff (m d₀:ℕ) (θ:ℝ) (hθ:0<θ):
    ∃ d:ℕ,d₀≤d ∧ 2≤d ∧ (1/((m:ℝ)+1))/(d:ℝ)≤θ:=by
  obtain ⟨N,hN⟩:=exists_nat_gt (1/θ)
  let d:=max N (max d₀ 2)
  have hdN:N≤d:=le_max_left _ _
  have hdd:d₀≤d:=(le_max_left _ _).trans (le_max_right _ _)
  have hd2:2≤d:=(le_max_right _ _).trans (le_max_right _ _)
  have hdR:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hNd:(N:ℝ)≤d:=by exact_mod_cast hdN
  have hratio:1/θ<(d:ℝ):=hN.trans_le hNd
  have hθd:1≤θ*d:=by
    have hh:1<(d:ℝ)*θ:=(div_lt_iff₀ hθ).mp hratio
    nlinarith
  have hc:(1:ℝ)≤(m:ℝ)+1:=by exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hrec:1/((m:ℝ)+1)≤1:=by
    apply (div_le_iff₀ (by positivity:0<(m:ℝ)+1)).2
    linarith
  refine ⟨d,hdd,hd2,?_⟩
  apply (div_le_iff₀ hdR).2
  linarith
end Oberwolfach
