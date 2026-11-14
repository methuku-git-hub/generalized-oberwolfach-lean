module

public import Oberwolfach.LongAssignedHostMatchingWeights
public import Oberwolfach.VortexSizeBounds

@[expose] public section
/-! Numerical matching hypotheses follow from the regular host and its
original allowed-cycle threshold. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_regular_host_numeric_inputs
    (n D:ℕ) (hn:0<n) (U:Type) [Fintype U] (Allowed:Set ℕ)
    (hAllowed:Allowed.Nonempty) (hvalid:∀r∈Allowed,3≤r)
    (α:ℝ) (hα:0<α) (G:SimpleGraph (Fin n)) (hreg:G.IsRegularOfDegree D)
    (hmin:(allowedThreshold Allowed+α)*n≤(D:ℝ)):
    0<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧
    (1/2+α)*n≤(D:ℝ) ∧
    (∀v,|(G.degree v:ℝ)-D|≤(0:ℝ)*n) ∧
    initialIndexDensity U D*(D:ℝ)=2*Fintype.card U := by
  have hhalf:1/2≤allowedThreshold Allowed:=allowedThreshold_half_le hAllowed hvalid
  have hnR:0<(n:ℝ):=by exact_mod_cast hn
  have hmin':(1/2+α)*n≤(D:ℝ):=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)+α≤allowedThreshold Allowed+α by linarith) hnR.le
    exact hh.trans hmin
  have hD:0<D:=by
    have hh:0<(D:ℝ):=lt_of_lt_of_le (by positivity) hmin'
    exact_mod_cast hh
  have hhalfD:(n:ℝ)/2≤D:=by nlinarith [mul_nonneg hα.le hnR.le]
  have hDhiN:D≤n:=by simpa using (regular_degree_le_card hreg (by simpa using hn))
  have hDhi:(D:ℝ)≤n:=by exact_mod_cast hDhiN
  refine ⟨hD,hhalfD,(by linarith),hmin',?_,?_⟩
  · intro v
    rw [hreg v]
    simp
  · have hD0:(D:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt hD)
    dsimp [initialIndexDensity]
    field_simp
end Oberwolfach
