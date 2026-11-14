module

public import Oberwolfach.LongCompatibleParameterChoices

@[expose] public section
/-! Matching tolerances can be chosen after any fixed positive spacing. -/
set_option autoImplicit false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach

theorem long_matching_fixed_spacing_parameters
    (K d:ℕ) (hK:0<K) (hd:0<d) (θ lam:ℝ) (hθ:0<θ) (hlam:0<lam):
    ∃eps:ℝ,0<eps ∧ eps≤1 ∧ 3*eps≤lam*(θ/(100*(K:ℝ)^2)) ∧
      let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
      let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
      0<alpha ∧ alpha≤θ/(200*(K:ℝ)^2) ∧ 0<γ ∧ γ≤eps:=by
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  let eps:ℝ:=min (1/2) (lam*θ/(600*(K:ℝ)^2))
  have heps:0<eps:=lt_min (by norm_num) (by positivity)
  have heps1:eps≤1:=by have hh:=min_le_left (1/2:ℝ) (lam*θ/(600*(K:ℝ)^2));dsimp [eps];linarith
  have hepsAssign:3*eps≤lam*(θ/(100*(K:ℝ)^2)):=by
    have hh:eps≤lam*θ/(600*(K:ℝ)^2):=min_le_right _ _
    have heq:lam*(θ/(100*(K:ℝ)^2))=6*(lam*θ/(600*(K:ℝ)^2)):=by ring
    rw [heq]
    have hp:0≤lam*θ/(600*(K:ℝ)^2):=by positivity
    linarith
  refine ⟨eps,heps,heps1,hepsAssign,?_⟩
  dsimp only
  refine ⟨lt_min (by positivity) (by positivity),min_le_right _ _,?_,?_⟩
  · exact lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))
  · have hh:=min_le_left (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    linarith
end Oberwolfach
