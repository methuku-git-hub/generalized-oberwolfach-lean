module

public import Oberwolfach.ReservedSpokeIndependentMargins
public import Oberwolfach.AbsorberSpacingParameterChoice

@[expose] public section
/-! Choose fixed reserved-list and matching margins before the cycle spacing. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem reserved_matching_parameter_order
    (γ p ρ η:ℝ) (hγ:0<γ) (hp:0<p) (hρ:0<ρ) (hρ1:ρ≤1) (hη:0<η):
    ∃βraw β θ δ αcap b:ℝ,
      0<βraw ∧ 0<β ∧ β≤1 ∧ βraw=4*β ∧
      0<θ ∧ θ≤η ∧ θ≤1/100 ∧ 0<δ ∧ 10*θ≤δ ∧ δ≤(β/100)^2 ∧
      αcap=ρ/40000 ∧ 0<αcap ∧ b=αcap*θ/2048 ∧ 0<b ∧ b≤αcap/16 ∧ b≤δ/4 ∧
      (∃N:ℕ,∀n:ℕ,N≤n→βraw*n+(n:ℝ)^(3/4:ℝ)≤γ*p^2*n/100) ∧
      (∃M:ℕ,∀m:ℕ,M≤m→0<m ∧ 4/(m:ℝ)≤b/2 ∧ 1/(100*(m:ℝ))≤β/4 ∧
        ∃N:ℕ,∀n:ℕ,N≤n→4*(n:ℝ)^(3/4:ℝ)≤b*n/2):=by
  obtain ⟨βraw,β,θ,δ,hβraw,hβ,hβ1,hratio,hθ,hθη,hθ1,hδ,hθδ,hδbound,N,hN⟩:=
    reserved_spoke_independent_margins γ p η hγ hp hη
  let αcap:=ρ/40000
  let b:=αcap*θ/2048
  have hα:0<αcap:=by dsimp [αcap];positivity
  have hα1:αcap≤1:=by dsimp [αcap];linarith
  have hb:0<b:=by dsimp [b];positivity
  have hbα:b≤αcap/16:=by dsimp [b];nlinarith
  have hbδ:b≤δ/4:=by dsimp [b];nlinarith
  obtain ⟨M,hM⟩:=absorber_spacing_parameter_choice β b hβ hb
  exact ⟨βraw,β,θ,δ,αcap,b,hβraw,hβ,hβ1,hratio,hθ,hθη,hθ1,hδ,hθδ,hδbound,rfl,hα,rfl,hb,hbα,hbδ,⟨N,hN⟩,⟨M,hM⟩⟩
end Oberwolfach
