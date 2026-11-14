module

public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The finite family of seed root tests has a vanishing failure budget
when its number is polynomial and every exponent has a fixed positive rate. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem eventually_polynomial_exponential_failure_below
    (C c δ:ℝ) (hc:0<c) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→C*(n:ℝ)^2*Real.exp (-c*(n:ℝ))<δ :=by
  obtain ⟨N₁,hN₁⟩:=eventually_stretchedExp_le_inv_pow C 2 (c:=c) (p:=1) hc (by norm_num) 1
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt (1/δ)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn
  have hn1:N₁≤n:=le_trans (le_max_left _ _) hn
  have hn2:N₂≤n:=le_trans (le_max_right _ _) hn
  have hn2r:(N₂:ℝ)≤n:=by exact_mod_cast hn2
  have hnpos:0<(n:ℝ):=by
    have hh:0<1/δ:=by positivity
    linarith
  have hinv:1/(n:ℝ)<δ:=by
    apply (div_lt_iff₀ hnpos).2
    have hh:(1/δ)<(n:ℝ):=lt_of_lt_of_le hN₂ hn2r
    have hh':1<δ*(n:ℝ):=by simpa [mul_comm] using (div_lt_iff₀ hδ).1 hh
    nlinarith
  have h:=hN₁ n hn1
  simp only [Real.rpow_two,Real.rpow_one,pow_one] at h
  exact h.trans_lt hinv
theorem eventually_any_polynomial_exponential_failure_below
    (C c δ:ℝ) (q:ℕ) (hc:0<c) (hδ:0<δ):
    ∃N:ℕ,∀n:ℕ,N≤n→C*(n:ℝ)^q*Real.exp (-c*(n:ℝ))<δ :=by
  obtain ⟨N₁,hN₁⟩:=eventually_stretchedExp_le_inv_pow C (q:ℝ) (c:=c) (p:=1) hc (by norm_num) 1
  obtain ⟨N₂,hN₂⟩:=exists_nat_gt (1/δ)
  refine ⟨max N₁ N₂,?_⟩
  intro n hn
  have hn1:N₁≤n:=le_trans (le_max_left _ _) hn
  have hn2:N₂≤n:=le_trans (le_max_right _ _) hn
  have hn2r:(N₂:ℝ)≤n:=by exact_mod_cast hn2
  have hnpos:0<(n:ℝ):=by
    have hh:0<1/δ:=by positivity
    linarith
  have hinv:1/(n:ℝ)<δ:=by
    apply (div_lt_iff₀ hnpos).2
    have hh:(1/δ)<(n:ℝ):=lt_of_lt_of_le hN₂ hn2r
    have hh':1<δ*(n:ℝ):=by simpa [mul_comm] using (div_lt_iff₀ hδ).1 hh
    nlinarith
  have h:=hN₁ n hn1
  simp only [Real.rpow_natCast,Real.rpow_one,pow_one] at h
  exact h.trans_lt hinv
end Oberwolfach
