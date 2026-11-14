module

public import Oberwolfach.MarkedVortexInitialPotentialTransfer

@[expose] public section
/-! Fix the physical-change cap before sampling so the parent potential
uses only half of the final initial-level allowance. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem marked_initial_potential_change_budget
    (m:ℕ) (κ B pstar:ℝ) (hκ:0<κ) (hB:0≤B) (hpstar:0<pstar):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
      (κ/2)/4+33*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))*ζ≤κ/4 :=by
  let C:ℝ:=33*((m:ℝ)+1)^4*(2*B/pstar^(2*m+1))
  have hC:0≤C:=by dsimp [C];positivity
  let cap:=κ/(8*(C+1))
  have hcap:0<cap:=by dsimp [cap];positivity
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap
  have hmul:ζ*(8*(C+1))≤κ:=(le_div_iff₀ (by positivity)).mp hζcap
  have hz:0≤ζ:=hζ
  have hnon:0≤C*ζ:=mul_nonneg hC hz
  dsimp only [C] at hmul hnon ⊢
  nlinarith
end Oberwolfach
