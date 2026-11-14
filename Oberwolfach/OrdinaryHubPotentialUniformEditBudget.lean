module

public import Oberwolfach.OrdinaryAdaptiveHubWeightsLevelEvent

@[expose] public section
/-! Positive concentration and edit rates can be chosen before the domain
size, giving the exact local potential-error inequality at every level. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem ordinary_hub_potential_uniform_edit_budget
    (m:ℕ) (pmin cHi ξ:ℝ) (hpmin:0<pmin) (hcHi:0<cHi) (hξ:0<ξ):
    ∃t ζ:ℝ,0<t ∧ 0<ζ ∧
    ∀A L:ℝ,0<A→0≤L→L≤ζ*A→
    let Bpot:=4*cHi/pmin^(3*m+1);
    t+((m+1:ℕ):ℝ)^2*Bpot*L/A+
      2*(3*((m+1:ℕ):ℝ)^4*Bpot*L/A)≤ξ:=by
  let Bpot:ℝ:=4*cHi/pmin^(3*m+1)
  let C:ℝ:=((m+1:ℕ):ℝ)^2*Bpot+6*((m+1:ℕ):ℝ)^4*Bpot
  let t:ℝ:=ξ/4
  let ζ:ℝ:=ξ/(4*(C+1))
  have hB:0<Bpot:=by dsimp [Bpot];positivity
  have hC:0≤C:=by dsimp [C];positivity
  have ht:0<t:=by dsimp [t];positivity
  have hζ:0<ζ:=by dsimp [ζ];positivity
  have hζC:ζ*(C+1)=ξ/4:=by
    dsimp [ζ]
    have hh:(4*(C+1):ℝ)≠0:=by positivity
    field_simp
  refine ⟨t,ζ,ht,hζ,?_⟩
  intro A L hA hL hLA Bpot'
  have hratio:L/A≤ζ:=(div_le_iff₀ hA).mpr (by nlinarith only [hLA])
  have hbound:=mul_le_mul_of_nonneg_left hratio hC
  have hζ0:0≤ζ:=hζ.le
  have hζbound:ζ*C≤ξ/4:=by nlinarith only [hζC,hζ0]
  have hfinal:C*(L/A)≤ξ/4:=hbound.trans (by simpa only [mul_comm] using hζbound)
  change t+((m+1:ℕ):ℝ)^2*Bpot*L/A+
    2*(3*((m+1:ℕ):ℝ)^4*Bpot*L/A)≤ξ
  have heq:t+((m+1:ℕ):ℝ)^2*Bpot*L/A+
      2*(3*((m+1:ℕ):ℝ)^4*Bpot*L/A)=t+C*(L/A):=by dsimp [C];ring
  rw [heq]
  dsimp [t]
  linarith only [hfinal,hξ]
end Oberwolfach
