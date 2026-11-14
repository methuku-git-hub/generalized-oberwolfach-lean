module

public import Oberwolfach.LongNamedMatchingCorrectionRetainedProtectedProbability

@[expose] public section

/-! A sufficiently long marked cycle supplies the list-trimming inequality
for the early matching event, with the threshold chosen from the original
positive density and host-margin parameters. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_early_matching_list_trim_threshold
    (αRef ρ₀:ℝ) (hα:0<αRef) (hρ:0<ρ₀) :
    ∃M:ℕ,1≤M ∧ ∀m:ℕ,M≤m→
      1/(100*(m:ℝ))≤((min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16)/16 := by
  let β:ℝ:=(min (2*αRef) (1/4:ℝ))*(ρ₀/200)^2*(1/100)/16
  have hβ:0<β:=by dsimp [β];positivity
  obtain ⟨M,hM⟩:=exists_nat_gt (16/(100*β))
  refine ⟨max M 1,le_max_right _ _,?_⟩
  intro m hm
  have hmpos:0<(m:ℝ):=by exact_mod_cast (show 0<m by omega)
  have hMle:(M:ℝ)≤m:=by exact_mod_cast (show M≤m by omega)
  have hnum:(16:ℝ)≤(100*β)*(m:ℝ):=by
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0<100*β)).mp (le_trans hM.le hMle)
  have hres:1/(100*(m:ℝ))≤β/16:=by
    apply (div_le_iff₀ (by positivity : 0<100*(m:ℝ))).mpr
    nlinarith
  exact hres
end Oberwolfach
