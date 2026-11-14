module

public import Oberwolfach.RawIntervalParameters

@[expose] public section
/-! The raw interval law implies the upper probability bounds used in seed
normalization, without assuming positivity of any marked marginal. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem raw_seed_probability_upper_bounds {U Γ Color:Type}
    [Fintype Γ] [Fintype Color]
    (d:ℕ) (p k:ℝ) (hp:0≤p) (hk:0≤k) (hpk:2*p+2*k≤1)
    (q:U→Γ→ℝ) (hq:∀u g,0≤q u g)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j)
    (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑g,q u g)):
    p≤1 ∧ k≤1 ∧ ∀u j,s u j≤1:=by
  constructor
  · linarith
  constructor
  · linarith
  · intro u j
    have hqsum:0≤∑g,q u g:=Finset.sum_nonneg (fun g _=>hq u g)
    have hinv:0≤1/(d:ℝ):=by positivity
    have hle:intervalUncoveredProbability d (∑g,q u g)≤1:=by
      unfold intervalUncoveredProbability
      have hprod:=mul_nonneg (show 0≤1+1/(d:ℝ) by linarith) hqsum
      linarith
    have hj:s u j≤∑j,s u j:=Finset.single_le_sum (fun i _=>hs u i) (Finset.mem_univ j)
    exact hj.trans ((hS u).trans hle)
end Oberwolfach
