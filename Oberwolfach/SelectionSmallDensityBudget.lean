module

public import Oberwolfach.IndexedGraphSelection

@[expose] public section

/-! Selection and the later graph deletion use the same fixed sample.
The density can be chosen below any subsequently specified upper bound;
the order threshold absorbs integer rounding in the selection cap. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem indexed_selection_small_density_budget (C ζ:ℝ) (hC:0<C) (hζ:0<ζ):
    ∃ p₀:ℝ,0<p₀∧p₀≤1∧∀ p:ℝ,0<p→p≤p₀→∃ N:ℕ,∀ n:ℕ,N≤n→
    ∀ δ:ℝ,δ≤ζ*p*n/2→
      4*(C*p*Real.sqrt (C*p)*n)+4*(Nat.ceil (4*(C*p*Real.sqrt (C*p)*n)):ℝ)+δ≤ζ*p*n := by
  let a:=ζ/(80*C*Real.sqrt C)
  have ha:0<a:=by dsimp [a];positivity
  refine ⟨min 1 (a^2),lt_min (by norm_num) (pow_pos ha _),min_le_left _ _,?_⟩
  intro p hp hpp
  have hs:Real.sqrt p≤a:=(Real.sqrt_le_left ha.le).mpr (hpp.trans (min_le_right _ _))
  have hsmall:20*(C*p*Real.sqrt (C*p))≤ζ*p/4:=by
    rw [Real.sqrt_mul hC.le]
    have hmul:=mul_le_mul_of_nonneg_left hs (show 0≤80*C*Real.sqrt C by positivity)
    have heq:(80*C*Real.sqrt C)*a=ζ:=by dsimp [a];field_simp
    rw [heq] at hmul
    have hh:=mul_le_mul_of_nonneg_right hmul hp.le
    nlinarith only [hh]
  refine ⟨Nat.ceil (16/(ζ*p)),?_⟩
  intro n hn δ hδ
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hnlow:16/(ζ*p)≤(n:ℝ):=(Nat.le_ceil _).trans (Nat.cast_le.mpr hn)
  have hscale:16≤ζ*p*n:=by
    have hh:=(div_le_iff₀ (mul_pos hζ hp)).mp hnlow
    nlinarith only [hh]
  have hceil:(Nat.ceil (4*(C*p*Real.sqrt (C*p)*n)):ℝ)≤4*(C*p*Real.sqrt (C*p)*n)+1:=
    (Nat.ceil_lt_add_one (by positivity)).le
  have he:=mul_le_mul_of_nonneg_right hsmall hn0
  nlinarith only [hceil,he,hδ,hscale]

end Oberwolfach
