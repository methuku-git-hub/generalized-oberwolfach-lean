module

public import Oberwolfach.MarkedExpandedRawCommonEvent

@[expose] public section
/-! Feasible interval probabilities have ordinary marginals at most one. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach

theorem interval_spoke_marginals_at_most_one {U Γ Color:Type} [Fintype Γ] [Fintype Color]
    (d:ℕ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
    (hq:∀ u g,0≤q u g) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)):
    ∀ u j,s u j≤1:=by
  intro u j
  have hsingle:s u j≤∑ j,s u j:=Finset.single_le_sum (fun i _=>hs u i) (Finset.mem_univ j)
  have hQ0:0≤∑ g,q u g:=Finset.sum_nonneg (fun i _=>hq u i)
  have hfactor:0≤(1+1/(d:ℝ))*(∑ g,q u g):=mul_nonneg (by positivity) hQ0
  have hh:=hS u
  unfold intervalUncoveredProbability at hh
  linarith
end Oberwolfach
