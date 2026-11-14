module

public import Oberwolfach.LongHubFrequencyParameters

@[expose] public section
/-! Choose the root-load tolerances after the matching theorem has supplied
its threshold, keeping all previously chosen frequency margins. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach

theorem long_hub_matching_error_margins (K:ℕ) (θ eps η:ℝ)
    (hK:0<K) (hθ:0<θ) (heps:0<eps) (hη:0<η):
    ∃t τ:ℝ, 0<t ∧ 0<τ ∧ t+4*τ≤eps/2 ∧ t≤θ/(800*(K:ℝ)) ∧
      ((K:ℝ)+1)*t+τ≤η :=by
  have hK:0<(K:ℝ):=by exact_mod_cast hK
  let t:ℝ:=min (θ/(1600*(K:ℝ))) (min (eps/8) (η/(4*((K:ℝ)+1))))
  let τ:ℝ:=min (eps/16) (η/4)
  have ht:0<t:=by dsimp [t];positivity
  have hτ:0<τ:=by dsimp [τ];positivity
  have htθ:t≤θ/(1600*(K:ℝ)):=min_le_left _ _
  have hte:t≤eps/8:=le_trans (min_le_right _ _) (min_le_left _ _)
  have htη:t≤η/(4*((K:ℝ)+1)):=le_trans (min_le_right _ _) (min_le_right _ _)
  have hτe:τ≤eps/16:=min_le_left _ _
  have hτη:τ≤η/4:=min_le_right _ _
  refine ⟨t,τ,ht,hτ,by linarith,?_,?_⟩
  · apply le_trans htθ
    have hp:0<800*(K:ℝ):=by positivity
    have hp2:0<1600*(K:ℝ):=by positivity
    apply (div_le_div_iff₀ hp2 hp).2
    nlinarith
  · have hp:0<4*((K:ℝ)+1):=by positivity
    have hh: t*(4*((K:ℝ)+1))≤η:=(le_div_iff₀ hp).1 htη
    nlinarith
end Oberwolfach
