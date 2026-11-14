module

public import Oberwolfach.RawIntervalParameters

@[expose] public section
/-! The two selected interval colours and two spoke colours obey the raw
interval-law hypotheses under the long preparation's explicit residual bound. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_preparation_interval_feasible {U:Type} [Fintype U]
    (d:ℕ) (hd:2≤d) (t s₀:ℝ) (ht:0≤t) (hs₀:0≤s₀)
    (a b:U→ℝ) (ha:∀ u,0≤a u) (hb:∀ u,0≤b u)
    (hinterval:∀ u,t+a u≤1/8)
    (hrest:∀ u,(t+a u)/(d:ℝ)≤1-s₀-t-a u-b u):
    let q:=fun (u:U) (j:Bool)=>if j then a u else t
    let s:=fun (u:U) (j:Bool)=>if j then b u else s₀;
    (∀ u j,0≤q u j) ∧ (∀ u,∑ j,q u j≤1/8) ∧
    (∀ u j,0≤s u j) ∧ (∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ j,q u j)):=by
  intro q s
  refine ⟨?_,?_,?_,?_⟩
  · intro u j
    cases j <;> simp [q,ht,ha]
  · intro u
    simpa [q,Fintype.sum_bool,add_comm] using hinterval u
  · intro u j
    cases j <;> simp [s,hs₀,hb]
  · intro u
    have h:=hrest u
    have heq:(1+1/(d:ℝ))*(t+a u)=t+a u+(t+a u)/(d:ℝ):=by ring
    simp only [q,s,Fintype.sum_bool,Bool.false_eq_true,ite_false,ite_true,intervalUncoveredProbability]
    rw [add_comm (a u) t,heq]
    linarith
end Oberwolfach
