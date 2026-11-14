module

public import Oberwolfach.ClassRoutingChooseScalesBounded

@[expose] public section
/-! Routing and discrepancy scales can be chosen before the order so the
class correction fits an independently fixed deletion budget. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem class_routing_fits_deletion (β δ:ℝ) (hβ:0<β) (hδ:0<δ):
    ∃q c:ℝ,0<q ∧ 0<c ∧ ∃N:ℕ,1≤N ∧ ∀n:ℕ,N≤n→∀a f b ζ:ℝ,
      0≤a→a≤c*n→f≤ζ*n→ζ≤β/16→b≤(δ/16)*n→
      ∃L:ℕ,0<L ∧ (n:ℝ)*a/L+2*a+4*L+2*f<β*n ∧ b+a+2*L≤δ*n:=by
  obtain ⟨q,c,hq,hc,hqδ,hcδ,hgap⟩:=class_routing_choose_scales_bounded β δ hβ hδ
  have hζgap:=hgap (β/16) (le_refl _)
  obtain ⟨N,hNpos,hN⟩:=class_routing_linear_margins c q (β/16) β hc.le hq hζgap
  refine ⟨q,c,hq,hc,max N ⌈4/δ⌉₊,le_trans hNpos (le_max_left _ _),?_⟩
  intro n hn a f b ζ ha hac hf hζ hb
  have hn0:0≤(n:ℝ):=Nat.cast_nonneg n
  have hnN:N≤n:=(le_max_left _ _).trans hn
  have hζn:=mul_le_mul_of_nonneg_right hζ hn0
  have hf':f≤(β/16)*n:=by linarith
  obtain ⟨hLpos,hrout,hL⟩:=hN n hnN a f ha hac hf'
  refine ⟨Nat.ceil (q*n),hLpos,hrout,?_⟩
  have hceil:(4/δ:ℝ)≤n:=(Nat.le_ceil _).trans (by exact_mod_cast ((le_max_right _ _).trans hn : ⌈4/δ⌉₊≤n))
  have hnlarge:4≤δ*n:=by exact (div_le_iff₀ hδ).mp hceil |>.trans_eq (mul_comm _ _)
  have hcN:=mul_le_mul_of_nonneg_right hcδ hn0
  have hqN:=mul_le_mul_of_nonneg_right hqδ hn0
  nlinarith
end Oberwolfach
