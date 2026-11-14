module

public import Mathlib.Tactic

@[expose] public section
/-! The triangle root-cover degree bound fits a later preselected local
budget when the cover load, deeper roots and balance error are small. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_root_cover_budget
    (γ κ lam ηbal ε N A I T W:ℝ)
    (hγ:0<γ) (hκ:0≤κ) (hlam:0≤lam) (hη:0≤ηbal) (hε:0≤ε)
    (hN:0≤N) (hA:N/2≤A) (hI:0≤I) (hIcap:I≤ε*N)
    (hT:0≤T) (hW:0≤W) (hroots:T+W≤lam*N)
    (hκcap:κ≤γ/1000) (hlamcap:lam≤γ/100) (hbalcap:ηbal*ε≤γ/8):
    let ell:=max (18*κ*N+3*(W+T)) (9*κ*N+3*T)
    let bin:=ηbal*I
    let f:=T+2*W
    let binner:=bin+3*ell+f;
    0≤ell ∧ 0≤bin ∧ 0≤f ∧ 0≤binner ∧
    f≤γ*A ∧ binner≤γ*A ∧ ell≤γ*A :=by
  intro ell bin f binner
  have hκN:=mul_le_mul_of_nonneg_right hκcap hN
  have hlamN:=mul_le_mul_of_nonneg_right hlamcap hN
  have hbalN:=mul_le_mul_of_nonneg_right hbalcap hN
  have hIη:=mul_le_mul_of_nonneg_left hIcap hη
  have hγN:0≤γ*N:=mul_nonneg hγ.le hN
  have hell0:0≤ell:=by
    dsimp [ell]
    exact le_trans (by positivity : (0:ℝ)≤18*κ*N+3*(W+T)) (le_max_left _ _)
  have hell:ell≤(1/10:ℝ)*γ*N:=by
    dsimp [ell]
    apply max_le <;> nlinarith only [hκN,hlamN,hroots,hT,hW,hγN]
  have hbin:bin≤(1/8:ℝ)*γ*N:=by
    dsimp [bin]
    nlinarith only [hIη,hbalN]
  have hf:f≤(1/50:ℝ)*γ*N:=by
    dsimp [f]
    nlinarith only [hroots,hT,hW,hlamN]
  have hγA:γ*N/2≤γ*A:=by nlinarith [mul_le_mul_of_nonneg_left hA hγ.le]
  have hbin0:0≤bin:=by dsimp [bin];positivity
  have hf0:0≤f:=by dsimp [f];positivity
  have hb0:0≤binner:=by dsimp [binner];positivity
  refine ⟨hell0,hbin0,hf0,hb0,?_,?_,?_⟩
  · nlinarith only [hf,hγA,hγN]
  · dsimp only [binner]
    nlinarith only [hbin,hell,hf,hγA,hγN]
  · nlinarith only [hell,hγA,hγN]
end Oberwolfach
