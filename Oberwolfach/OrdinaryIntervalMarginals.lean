module

public import Oberwolfach.RawIntervalParameters

@[expose] public section
/-! The selected and approximate ordinary pair marginals fit into the
positions not occupied by marked intervals. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem ordinary_interval_marginals_feasible (s a b u θ:ℝ) (d:ℕ) (hd:2≤d)
    (hθ:0<θ) (hda:1/θ≤d) (hs:0≤s) (ha:0≤a) (ha8:a≤1/8) (hb:0≤b)
    (hu:θ/2≤u) (hrow:s+a+b+u=1):
    let q:Bool→ℝ:=fun j=>if j then a else 0
    let t:Bool→ℝ:=fun j=>if j then b else s;
    (∀ j,0≤q j) ∧ (∑ j,q j)≤1/8 ∧ (∀ j,0≤t j) ∧
    (∑ j,t j) ≤ intervalUncoveredProbability d (∑ j,q j) := by
  intro q t
  have hd0:(0:ℝ)<d:=by exact_mod_cast (show 0<d by omega)
  have hθd:1≤θ*d:=by simpa only [mul_comm] using (div_le_iff₀ hθ).mp hda
  have habound:a/(d:ℝ)≤θ/8:=by
    apply (div_le_iff₀ hd0).2
    nlinarith
  have hroom:a/(d:ℝ)≤u:=by linarith
  refine ⟨?_,?_,?_,?_⟩
  · intro j;cases j <;> simp [q,ha]
  · simpa [q] using ha8
  · intro j;cases j <;> simp [t,hs,hb]
  · simp [q,t,intervalUncoveredProbability]
    have hroom':((d:ℝ)⁻¹)*a≤u:=by simpa [div_eq_mul_inv,mul_comm] using hroom
    nlinarith only [hrow,hroom']
end Oberwolfach
