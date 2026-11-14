module

public import Oberwolfach.OrdinaryCleanupMarginHierarchy

@[expose] public section
/-! Choose the endpoint size before the fresh pairing theorem supplies its
    accuracy, then choose the edit tolerance after that accuracy is known. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem ordinary_pairing_ordered_hierarchy
    (p₀ κ K:ℝ) (hp₀:0<p₀) (hκ:0<κ) (hK:0<K):
    ∃a:ℝ,0<a ∧ a≤1 ∧
      ∀η:ℝ,0<η→∃lam:ℝ,0<lam ∧
        a*K+2*lam≤p₀/2 ∧ a*K+2*lam≤p₀*κ ∧ 6*lam≤η*a:=by
  let a:=min (1/2:ℝ) (min (p₀/(16*K)) (p₀*κ/(8*K)))
  have ha:0<a:=by dsimp [a];positivity
  have ha1:a≤1:=by have hh:=min_le_left (1/2:ℝ) (min (p₀/(16*K)) (p₀*κ/(8*K)));dsimp only [a];linarith
  have haR:a≤p₀/(16*K):=(min_le_right _ _).trans (min_le_left _ _)
  have haH:a≤p₀*κ/(8*K):=(min_le_right _ _).trans (min_le_right _ _)
  have haRK:a*K≤p₀/16:=by
    have hh:=(le_div_iff₀ (show 0<16*K by positivity)).mp haR
    nlinarith only [hh]
  have haHK:a*K≤p₀*κ/8:=by
    have hh:=(le_div_iff₀ (show 0<8*K by positivity)).mp haH
    nlinarith only [hh]
  refine ⟨a,ha,ha1,?_⟩
  intro η hη
  let lam:=min (p₀/16) (min (p₀*κ/16) (η*a/12))
  have hlam:0<lam:=by dsimp [lam];positivity
  have hlamR:lam≤p₀/16:=min_le_left _ _
  have hlamH:lam≤p₀*κ/16:=(min_le_right _ _).trans (min_le_left _ _)
  have hlamη:lam≤η*a/12:=(min_le_right _ _).trans (min_le_right _ _)
  refine ⟨lam,hlam,?_,?_,?_⟩
  · linarith
  · have hpκ:0<p₀*κ:=mul_pos hp₀ hκ;linarith
  · linarith
end Oberwolfach
