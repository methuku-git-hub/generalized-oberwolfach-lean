module

public import Oberwolfach.LongMatchingFixedSpacingParameters

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_ordered_matching_residual_rates
    (K d:ℕ) (hK:0<K) (hd:0<d) (θ lam eps:ℝ)
    (hθ:0<θ) (hlam:0<lam) (heps:0<eps):
    let alpha:=min (lam/(10*(d:ℝ))) (θ/(200*(K:ℝ)^2))
    let γ:=min (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)));
    0≤alpha ∧ 0≤γ ∧ alpha≤lam/(10*d) ∧ γ≤lam/(10*d) ∧
      γ≤lam/10 ∧ γ≤eps ∧ γ≤1/2 := by
  have hKR:(0:ℝ)<K:=by exact_mod_cast hK
  have hdR:(0:ℝ)<d:=by exact_mod_cast hd
  dsimp only
  refine ⟨le_of_lt (lt_min (by positivity) (by positivity)),
    le_of_lt (lt_min (by positivity) (lt_min (by norm_num) (lt_min (by positivity) (by positivity)))),
    min_le_left _ _,?_,?_,?_,?_⟩
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  · have h:=min_le_left (eps/2) (min (1/2:ℝ) (min (lam/(10*(d:ℝ))) (lam/10)))
    linarith
  · exact (min_le_right _ _).trans (min_le_left _ _)
end Oberwolfach
