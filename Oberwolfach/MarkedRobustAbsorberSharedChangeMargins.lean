module

public import Oberwolfach.CommonWitnessMargins

@[expose] public section
/-! One positive change tolerance supplies all error and density margins
for corrected-host robust absorption, before choosing the graph or sample. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_robust_absorber_shared_change_margins
    (r:ℕ) (ε K bc bp ρ σ:ℝ) (hε:0<ε) (hK:0≤K)
    (hbc:0<bc) (hbp:0<bp) (hρ:0<ρ) (hσ:0<σ):
    ∃ cap:ℝ,0<cap ∧ ∀ ζ:ℝ,0≤ζ→ζ≤cap→
      2*ζ≤ε/4 ∧ 4*ζ≤ε/4 ∧ K*ζ≤ε/4 ∧
      3*(r+5:ℕ)*ζ≤bc ∧ 4*(r+5:ℕ)*ζ≤bp ∧
      4*ζ≤ρ ∧ (r+11:ℕ)*ζ≤σ:=by
  let cap:=min (ε/16) (min (ε/(4*(K+1)))
    (min (bc/(3*(r+5:ℕ))) (min (bp/(4*(r+5:ℕ))) (min (ρ/4) (σ/(r+11:ℕ))))))
  have hcap:0<cap:=by dsimp [cap];positivity
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hz
  have h1:ζ≤ε/16:=hz.trans (min_le_left _ _)
  have h2:ζ≤ε/(4*(K+1)):=hz.trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3:ζ≤bc/(3*(r+5:ℕ)):=hz.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have h4:ζ≤bp/(4*(r+5:ℕ)):=hz.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have h5:ζ≤ρ/4:=hz.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have h6:ζ≤σ/(r+11:ℕ):=hz.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  have hb2:ζ*(4*(K+1))≤ε:=(le_div_iff₀ (by positivity)).mp h2
  have hb3:ζ*(3*(r+5:ℕ))≤bc:=(le_div_iff₀ (by positivity)).mp h3
  have hb4:ζ*(4*(r+5:ℕ))≤bp:=(le_div_iff₀ (by positivity)).mp h4
  have hb6:ζ*(r+11:ℕ)≤σ:=(le_div_iff₀ (by positivity)).mp h6
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩ <;> push_cast at * <;> nlinarith
end Oberwolfach
