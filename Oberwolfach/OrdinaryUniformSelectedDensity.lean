module

public import Oberwolfach.FiniteHighEventsCommon

@[expose] public section
/-! A selected-edge and selected-spoke density floor chosen before the
actual class density and reserved fraction. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_uniform_selected_density_floor (ρ₀ s₀:ℝ)
    (hρ₀:0<ρ₀) (hρ₁:ρ₀≤1) (hs₀:0<s₀) (hs₁:s₀≤1):
    let pstar:=ρ₀*s₀/2;
    0<pstar ∧ pstar≤1 ∧ ∀ ρ s:ℝ,ρ₀≤ρ→ρ≤1→s₀/2≤s→s≤s₀→
      pstar≤ρ*s ∧ ρ*s≤1 ∧ pstar≤s ∧ s≤1 := by
  intro pstar
  have hp:0<pstar:=by dsimp [pstar];positivity
  have hp1:pstar≤1:=by dsimp [pstar];nlinarith [mul_nonneg (by linarith:0≤1-ρ₀) hs₀.le]
  refine ⟨hp,hp1,?_⟩
  intro ρ s hρlo hρhi hslo hshi
  have hs:0≤s:=by linarith
  have hρ:0≤ρ:=by linarith
  have hmul:=mul_le_mul_of_nonneg_right hρlo hs
  have hsbound:=mul_le_mul_of_nonneg_left hslo hρ₀.le
  have hupper:=mul_le_mul_of_nonneg_right hρhi hs
  have hbase:=mul_le_mul_of_nonneg_right hρ₁ (show (0:ℝ)≤s₀/2 by positivity)
  dsimp [pstar]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith
end Oberwolfach
