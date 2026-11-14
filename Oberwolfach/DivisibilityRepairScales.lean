module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Fixed switching capacity and an order threshold for every numerical
margin in the divisible-complement repair. All choices precede the graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem eventually_constant_le_linear (C c : ℝ) (hc : 0<c) :
    ∃ N : ℕ,∀ n : ℕ,N≤n → C≤c*n := by
  refine ⟨⌈C/c⌉₊,?_⟩
  intro n hn
  have hh : C/c≤(n:ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hm := (div_le_iff₀ hc).mp hh
  simpa only [mul_comm] using hm

theorem divisibility_repair_scales (q h : ℕ) (ρ ξ : ℝ) (hρ : 0<ρ) (hξ : 0<ξ) :
    ∃ L N : ℕ,0<L ∧ ∀ n : ℕ,N≤n → 0<n ∧
      (q:ℝ)*h≤(n:ℝ)/(4*(q+1:ℝ)) ∧
      (q:ℝ)*h≤ρ*n/2 ∧
      (q:ℝ)*n/L+4*q+4*L<(ρ/2)*n ∧
      (q:ℝ)*h+q+1≤ξ*n/4 := by
  let L : ℕ := ⌈8*q/ρ⌉₊+1
  have hL : 0<L := by dsimp [L];omega
  have hLr : (0:ℝ)<L := Nat.cast_pos.mpr hL
  have hrat : (q:ℝ)/L≤ρ/8 := by
    have hh : 8*(q:ℝ)/ρ≤(L:ℝ) := by
      have hc := Nat.le_ceil (8*(q:ℝ)/ρ)
      dsimp [L]
      push_cast
      linarith
    have hm := (div_le_iff₀ hρ).mp hh
    apply (div_le_iff₀ hLr).mpr
    nlinarith
  obtain ⟨N₁,h₁⟩ := eventually_constant_le_linear ((q:ℝ)*h) (1/(4*(q+1:ℝ))) (by positivity)
  obtain ⟨N₂,h₂⟩ := eventually_constant_le_linear ((q:ℝ)*h) (ρ/2) (by positivity)
  obtain ⟨N₃,h₃⟩ := eventually_constant_le_linear (4*(q:ℝ)+4*L) (ρ/8) (by positivity)
  obtain ⟨N₄,h₄⟩ := eventually_constant_le_linear ((q:ℝ)*h+q+1) (ξ/4) (by positivity)
  refine ⟨L,max (max N₁ N₂) (max N₃ N₄)+1,hL,?_⟩
  intro n hn
  have hnpos : 0<n := by omega
  have hnr : (0:ℝ)<n := Nat.cast_pos.mpr hnpos
  have ha := h₁ n (by omega)
  have hb := h₂ n (by omega)
  have hc := h₃ n (by omega)
  have hd := h₄ n (by omega)
  have hm := mul_le_mul_of_nonneg_right hrat hnr.le
  have hρn : 0<ρ*(n:ℝ) := mul_pos hρ hnr
  refine ⟨hnpos,?_,?_,?_,?_⟩
  · simpa only [one_div,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using ha
  · linarith only [hb]
  · have heq : (q:ℝ)/L*n=(q:ℝ)*n/L := by ring
    rw [heq] at hm
    linarith only [hm,hc,hρn]
  · linarith only [hd]

end Oberwolfach
