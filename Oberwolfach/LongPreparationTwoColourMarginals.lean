module

public import Oberwolfach.LongPreparationIntervalFeasible

@[expose] public section
/-! The selected colour uses the constant marginals required by the
reference theorem; the distinct approximate colour uses the hub marginals. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_two_colour_marginals {U:Type} [Fintype U]
    (d m:ℕ) (hd:2≤d) (hm:0<m) (s₀:ℝ) (hs₀:0≤s₀)
    (a b:U→ℝ) (ha:∀ u,0≤a u) (hb:∀ u,0≤b u)
    (hinterval:∀ u,s₀/(m:ℝ)+a u≤1/8)
    (hrest:∀ u,(s₀/(m:ℝ)+a u)/(d:ℝ)≤1-s₀-s₀/(m:ℝ)-a u-b u):
    let t:=s₀/(m:ℝ)
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let s:=fun (u:U) (j:Bool)=>if j then b u else s₀;
    (∀ u,q u false=s₀/(m:ℝ) ∧ q u true=a u ∧ s u false=s₀ ∧ s u true=b u) ∧
    (∀ u j,0≤q u j) ∧ (∀ u,∑ j,q u j≤1/8) ∧
    (∀ u j,0≤s u j) ∧ (∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ j,q u j)):=by
  intro t q s
  have ht:0≤t:=div_nonneg hs₀ (by positivity)
  have h:=long_preparation_interval_feasible d hd t s₀ ht hs₀ a b ha hb hinterval hrest
  dsimp only at h
  refine ⟨?_,h⟩
  intro u
  simp [q,s,t]
end Oberwolfach
