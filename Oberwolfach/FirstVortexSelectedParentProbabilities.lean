module

public import Oberwolfach.FirstVortexSeedDensityAlignment
public import Oberwolfach.LongAssignedSamplingRecipe

@[expose] public section
/-! Instantiate the probability and lower-density inputs of the first
selected parent with the exact sampling recipe. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem first_vortex_selected_parent_probabilities
    {n K:ℕ} {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (r:ℕ) (θ ρ₀ ρ:ℝ) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1):
    let m:ℝ:=(r+4:ℕ)
    let s₀:ℝ:=1/100
    let tstar:ℝ:=1/(200*m)
    let pstar:ℝ:=ρ₀/(800*m)
    let p:ℝ:=ρ*s₀/2
    let k:ℝ:=p/m;
    (∀u,longAssignedIntervalProbability F hF K (r+4) θ u false=s₀/m) ∧
    (∀u,longAssignedSpokeProbability F hF K (r+4) θ u false=s₀) ∧
    0<pstar ∧ pstar≤p ∧ pstar≤k ∧ pstar≤s₀ ∧ p≤1 ∧ k≤1 ∧ s₀≤1 ∧
    0<tstar ∧ tstar≤s₀/m ∧ pstar≤ρ*(s₀/m)/2 ∧
    ρ₀/400≤ρ*m*tstar/2 ∧ pstar≤ρ*m*tstar/2 ∧ pstar≤ρ*tstar/2 ∧ pstar≤tstar :=by
  intro m s₀ tstar pstar p k
  have h:=first_vortex_seed_density_alignment r ρ₀ ρ tstar hρ₀ hρlo hρhi (by dsimp [tstar,m]; exact le_rfl)
  obtain ⟨_,_,htstar,_,_,htcap,hpstar,_,hkcap,_,hp,hk,hs,hp1,hk1,hs1,hρ400,hkm,hkt,ht⟩:=h
  refine ⟨?_,?_,hpstar,hp,hk,hs,hp1,hk1,hs1,htstar,?_,?_,hρ400,hkm,hkt,ht⟩
  · intro u
    simp [longAssignedIntervalProbability,s₀,m]
  · intro u
    simp [longAssignedSpokeProbability,s₀]
  · simpa only [s₀,m] using htcap
  · simpa only [s₀,m] using hkcap
end Oberwolfach
