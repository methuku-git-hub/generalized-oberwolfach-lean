module

public import Oberwolfach.FirstVortexIndependentLoadScales
public import Oberwolfach.FirstVortexSpokeParameterFromLoad

@[expose] public section
/-! Independently chosen forced and free image loads satisfy the sharp
finite-size correction budget after a threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem first_vortex_independent_load_budget_eventually
    (host cap β:ℝ) (hhost:0<host) (hcap:0<cap) (hβ:0<β):
    ∃δsmall κ θ αAssign ρsmall ζsmall δspoke:ℝ,
      0<δsmall ∧ 0<κ ∧ 0<θ ∧ 0<αAssign ∧ 0<ρsmall ∧
      δsmall≤host ∧ θ≤1 ∧ 10*θ≤δsmall ∧ 10*θ≤κ*(β/4) ∧
      ρsmall≤θ/4096 ∧ 0≤ζsmall ∧ ζsmall≤θ/4096 ∧
      αAssign/16≤δsmall/4 ∧ 0≤δspoke ∧ δsmall+κ≤Real.sqrt δspoke ∧
      ∃N:ℕ,∀n:ℕ,N≤n→2*(δsmall*n+(κ*n+1))≤cap*n :=by
  obtain ⟨δsmall,κ,θ₀,hδ,hκ,hθ₀,hhostδ,hθδ,hθκ,hbudget⟩:=
    first_vortex_independent_load_scales host (cap/2) β hhost (by positivity) hβ
  let θ:=min θ₀ (1/2:ℝ)
  let αAssign:=δsmall
  let ρsmall:=θ/8192
  let ζsmall:ℝ:=0
  let δspoke:ℝ:=(δsmall+κ)^2
  have hθ:0<θ:=by dsimp [θ];positivity
  have hθle:θ≤θ₀:=min_le_left _ _
  have hθone:θ≤1:=by have h:=min_le_right θ₀ (1/2:ℝ);dsimp [θ];linarith
  have hscale:=first_vortex_spoke_parameter_from_load (δsmall+κ) (by positivity)
  obtain ⟨N,hN⟩:=exists_nat_gt (4/cap)
  refine ⟨δsmall,κ,θ,αAssign,ρsmall,ζsmall,δspoke,hδ,hκ,hθ,by dsimp [αAssign];exact hδ,by dsimp [ρsmall];positivity,hhostδ,hθone,?_,?_,?_,?_,?_,?_,?_,?_,N,?_⟩
  · linarith
  · linarith
  · dsimp [ρsmall];linarith
  · dsimp [ζsmall];norm_num
  · dsimp [ζsmall];positivity
  · dsimp [αAssign];linarith
  · exact hscale.1
  · exact hscale.2
  · intro n hn
    have hncast:(N:ℝ)≤n:=by exact_mod_cast hn
    have hncap:4≤cap*n:=by
      have hh:4/cap<(n:ℝ):=lt_of_lt_of_le hN hncast
      have hc:=mul_lt_mul_of_pos_right hh hcap
      have hc':4<cap*n:=by simpa [div_mul_cancel₀ _ (ne_of_gt hcap),mul_comm] using hc
      exact hc'.le
    have hbudgetn:=mul_le_mul_of_nonneg_right hbudget (show (0:ℝ)≤n by positivity)
    nlinarith
end Oberwolfach
