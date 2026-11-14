module

public import Oberwolfach.OrdinaryRootWheelApplication
public import Oberwolfach.ProtectedFactorPreparation

@[expose] public section
/-! The ambient graph and permutation-conflict hypotheses for the ordinary
reservoir are consequences of the regular host and threshold assumptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reservoir_regular_host_hypotheses {n D r d:ℕ}
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (hreg:P.IsRegularOfDegree D)
    (θ α ε:ℝ) (hθ:cycleThreshold r≤θ) (hmin:(θ+α)*n≤(D:ℝ)) (hε:0≤ε):
    (∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤6*d) ∧
    (∀v,(cycleThreshold r+α)*n≤(P.degree v:ℝ)) ∧
    (∀v,|(P.degree v:ℝ)-(D:ℝ)|≤ε*n):=by
  constructor
  · intro v
    have hh:=permutationConflictGraph_degree_le π (3*d) v
    have hh':(permutationConflictGraph π (3*d)).degree v≤6*d:=by omega
    exact_mod_cast hh'
  constructor
  · intro v
    have ha:cycleThreshold r+α≤θ+α:=by linarith
    have hh:(cycleThreshold r+α)*(n:ℝ)≤(θ+α)*n:=
      mul_le_mul_of_nonneg_right ha (by positivity)
    have hd:=hreg v
    have hd':(P.degree v:ℝ)=(D:ℝ):=by exact_mod_cast hd
    rw [hd']
    exact hh.trans hmin
  · intro v
    have hd:=hreg v
    have hd':(P.degree v:ℝ)=(D:ℝ):=by exact_mod_cast hd
    rw [hd']
    simp only [sub_self,abs_zero]
    exact mul_nonneg hε (by positivity)
end Oberwolfach
