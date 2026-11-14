module

public import Oberwolfach.OrdinaryTriangleSeparatedCoverEvent

@[expose] public section
/-! Choose a geometric scale before the independent prescribed-edge load.
The constants here are the explicit sufficient inequalities needed for the
separated root-cover packing; no relation between the two chosen scales is
required. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem ordinary_triangle_separated_numeric_scales
    (p γ ω θ ρ ρhub η : ℝ)
    (hp:0<p) (hγ:0<γ) (hω:0<ω) (hθ:0<θ) (hρ:0<ρ) (hρhub:0<ρhub) (hη:0<η):
    ∃b a₀:ℝ, 0<b ∧ 0<a₀ ∧
      6*b≤p^6*γ/4 ∧ 6*b≤(p^6*γ/4)*ω ∧
      b≤p^6*γ/8 ∧ b≤(p^6*γ/8)*ω ∧ b≤θ ∧
      2*b≤ω*p*η ∧
      ∀a:ℝ,0≤a→a≤a₀→b+12*a≤ρhub ∧ 3*b+24*a≤ρ/2 := by
  let A:ℝ:=p^6*γ
  have hA:0<A:=by dsimp [A]; positivity
  let b:ℝ:=min (A/24) (min (A*ω/24) (min θ (min (ω*p*η/2) (min (ρhub/2) (ρ/12)))))
  let a₀:ℝ:=min (ρhub/24) (ρ/96)
  have hb:0<b:=by dsimp [b]; positivity
  have ha₀:0<a₀:=by dsimp [a₀]; positivity
  have hb1:b≤A/24:=min_le_left _ _
  have hb2:b≤A*ω/24:=le_trans (min_le_right _ _) (min_le_left _ _)
  have hb3:b≤θ:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hb4:b≤ω*p*η/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hb5:b≤ρhub/2:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hb6:b≤ρ/12:=le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  have ha1:a₀≤ρhub/24:=min_le_left _ _
  have ha2:a₀≤ρ/96:=min_le_right _ _
  refine ⟨b,a₀,hb,ha₀,?_,?_,?_,?_,hb3,?_,?_⟩
  · dsimp [A] at hb1; linarith
  · dsimp [A] at hb2; linarith
  · dsimp [A] at hb1; linarith
  · dsimp [A] at hb2; linarith
  · linarith
  · intro a ha haa; constructor <;> linarith
end Oberwolfach
