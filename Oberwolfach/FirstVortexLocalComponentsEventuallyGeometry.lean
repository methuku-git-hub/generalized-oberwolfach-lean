module

public import Oberwolfach.FirstVortexActualLocalChainRates
public import Oberwolfach.ColourRoundErrorMargins

@[expose] public section
/-! The finite local component bounds follow from strict linear rate gaps. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_local_components_eventually_geometry
    (d:ℕ) (t b a γ κ Δ:ℝ) (ht:0<t)
    (hB:b+2*max a γ+κ<t) (hE:2*Δ<t):
    ∃N:ℕ,∀n:ℕ,N≤n→∀boundary:ℝ,boundary≤b*n→
      boundary+2*(max a γ*n)+((6*d+2:ℕ):ℝ)+(κ*n+1)≤t*n ∧
      (n:ℝ)^(3/5:ℝ)+2*Δ*n+2*(6*d+2:ℕ)≤t*n ∧ 1≤t*n :=by
  let gap:=min t (min (t-(b+2*max a γ+κ)) (t-2*Δ))
  have hgap:0<gap:=by dsimp [gap];exact lt_min ht (lt_min (by linarith) (by linarith))
  let C:ℝ:=2*(6*d+2:ℕ)+1
  have hC:0≤C:=by dsimp [C];positivity
  obtain ⟨N,hN⟩:=eventually_sublinear_affine_error 1 C 1 (2/5) gap
    (by norm_num) hC (by norm_num) (by norm_num) hgap
  refine ⟨N,?_⟩
  intro n hn boundary hb
  have herr:=hN n hn ((n:ℝ)^(3/5:ℝ)) (by norm_num)
  have hpow:0≤(n:ℝ)^(3/5:ℝ):=by positivity
  have hn0:(0:ℝ)≤n:=Nat.cast_nonneg _
  have hgapT:gap≤t:=min_le_left _ _
  have hgapB:gap≤t-(b+2*max a γ+κ):=(min_le_right _ _).trans (min_le_left _ _)
  have hgapE:gap≤t-2*Δ:=(min_le_right _ _).trans (min_le_right _ _)
  have hT:=mul_le_mul_of_nonneg_right hgapT hn0
  have hBr:=mul_le_mul_of_nonneg_right hgapB hn0
  have hEr:=mul_le_mul_of_nonneg_right hgapE hn0
  dsimp [C] at herr
  push_cast at herr ⊢
  constructor
  · nlinarith
  · constructor <;> nlinarith
end Oberwolfach
