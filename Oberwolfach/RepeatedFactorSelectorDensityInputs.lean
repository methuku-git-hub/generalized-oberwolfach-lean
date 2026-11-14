module

public import Oberwolfach.FirstVortexSelectedParentProbabilities
public import Oberwolfach.RepeatedFactorDensityOne

@[expose] public section
/-! The density-one repeated family satisfies the exact lower-density
requirements used by the selected marked sampler. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem repeated_factor_selector_density_inputs
    {n K D:ℕ} (F₀:SimpleGraph (Fin n)) (hF₀:F₀.IsRegularOfDegree 2)
    (r:ℕ) (θ ρ₀:ℝ) (hρ₀:0<ρ₀) (hρone:ρ₀≤1) (hD:0<D) (hEven:Even D):
    let ρ:=initialIndexDensity (Fin (D/2)) D
    let m:ℝ:=(r+4:ℕ)
    let pstar:=ρ₀/(800*m);
    ρ₀≤ρ ∧ ρ≤1 ∧ pstar≤ρ*(1/100)/2 ∧ pstar≤ρ*((1/100)/m)/2 :=by
  intro ρ m pstar
  have hρ:ρ=1:=repeated_factor_density_one D hD hEven
  have hprob:=first_vortex_selected_parent_probabilities (K:=K)
    (fun _:Fin (D/2)=>F₀) (fun _=>hF₀) r θ ρ₀ ρ hρ₀ (by rw [hρ]; exact hρone) (by rw [hρ])
  dsimp only [] at hprob
  obtain ⟨_,_,_,hp,_,_,_,_,_,_,_,hk,_,_,_,_⟩:=hprob
  exact ⟨by rw [hρ]; exact hρone,by rw [hρ],hp,hk⟩
end Oberwolfach
