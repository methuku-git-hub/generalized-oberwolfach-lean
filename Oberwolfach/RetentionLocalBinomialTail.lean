module

public import Oberwolfach.BinomialRestrictionMargins

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem retention_binomial_tail_at_local_scale
    (K a b:ℝ) (hK:0≤K) (ha:0<a) (hb:0<b) (L:ℕ):
    ∃N:ℕ,1≤N ∧ ∀M n:ℕ,N≤M→M≤n→∀p:ℝ,0≤p→p≤K*(n:ℝ)^(-b)→
      (M.choose (Nat.ceil (a*M)):ℝ)*p^(Nat.ceil (a*M))≤1/(M:ℝ)^L:=by
  obtain ⟨m,N,hm,hN,h⟩:=uniform_binomial_restriction_tail K a b hK ha hb L
  refine ⟨max m N,?_ ,?_⟩
  · exact le_trans hm (le_max_left m N)
  intro M n hM hMn p hp hrate
  have hM₁:m≤M:=le_trans (le_max_left m N) hM
  have hM₂:N≤M:=le_trans (le_max_right m N) hM
  have hMp:(0:ℝ)<M:=by exact_mod_cast (show 0<M by omega)
  have hMnR:(M:ℝ)≤n:=by exact_mod_cast hMn
  have hmono:(n:ℝ)^(-b)≤(M:ℝ)^(-b):=Real.rpow_le_rpow_of_nonpos hMp hMnR (by linarith)
  have hrate':p≤K*(M:ℝ)^(-b):=hrate.trans (mul_le_mul_of_nonneg_left hmono hK)
  exact h M hM₂ M hM₁ p hp hrate'
end Oberwolfach
