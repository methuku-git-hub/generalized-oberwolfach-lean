module

public import Oberwolfach.DivisibilityRepairScales
public import Oberwolfach.AsymptoticMargins

@[expose] public section
/-! The manuscript's displayed matching parameters meet the stricter
assignment hierarchy after the original spacing parameter is chosen large. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach

theorem long_manuscript_matching_parameters_exist
    (K m:ℕ) (hK:0<K) (θ lam:ℝ) (hθ:0<θ) (hlam:0<lam):
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
    ∃d₀:ℕ,∀d:ℕ,d₀≤d→2≤d ∧
      (1/((m:ℝ)+1))/(d:ℝ)≤θ ∧
      let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
      let γ:=min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10))
      0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps :=by
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  let eps:=min (1/2:ℝ) (lam*θ/(600*(K:ℝ)^2))
  have heps:0<eps:=lt_min (by norm_num) (by positivity)
  have heps1:eps≤1:=by have hh:eps≤1/2:=min_le_left _ _;linarith
  have hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have hh:eps≤lam*θ/(600*(K:ℝ)^2):=min_le_right _ _
    have heq:lam*(θ/(100*(K:ℝ)^2))=6*(lam*θ/(600*(K:ℝ)^2)):=by ring
    rw [heq]
    have hp:0≤lam*θ/(600*(K:ℝ)^2):=by positivity
    linarith
  obtain ⟨D₁,hD₁⟩:=eventually_constant_le_linear lam (10*eps) (by positivity)
  obtain ⟨D₂,hD₂⟩:=eventually_constant_le_linear (1/((m:ℝ)+1)) θ hθ
  refine ⟨eps,heps,heps1,hepsAssign,max (max D₁ D₂) 2,?_⟩
  intro d hd
  have hd2:2≤d:=by omega
  have hdpos:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
  have hLam:=hD₁ d (by omega)
  have hc:=hD₂ d (by omega)
  have hγsmall:lam/(10*(d:ℝ))≤eps:=by
    apply (div_le_iff₀ (by positivity : 0<10*(d:ℝ))).2
    nlinarith
  have hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ:=by
    apply (div_le_iff₀ hdpos).2
    nlinarith
  refine ⟨hd2,hcut,?_⟩
  dsimp only
  exact ⟨lt_min (by positivity) (by positivity),min_le_right _ _,
    lt_min (by norm_num) (lt_min (by positivity) (by positivity)),
    (min_le_right _ _).trans ((min_le_left _ _).trans hγsmall)⟩
end Oberwolfach
