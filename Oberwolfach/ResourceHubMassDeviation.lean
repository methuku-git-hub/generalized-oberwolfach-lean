module

public import Oberwolfach.RestrictedHubTestMass

@[expose] public section
/-! Sum root-load and hub-count errors to obtain the original fixed
coefficient-test mass, without changing the sample or the weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E U:Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq U]

theorem resource_hub_test_mass_deviation
    (R:E→Finset V) (w:E→ℝ) (hub:E→U) (u:U) (S:Finset V) (r:ℕ)
    (hS:∀e,(R e∩S).card=if hub e=u then r else 0)
    (η s n err countErr:ℝ) (hη:0≤η)
    (hdeg:∀v∈S,|hypergraphWeightedDegree R w v-η|≤err)
    (hcount:|((S.card:ℕ):ℝ)-s*n|≤countErr):
    |(r:ℝ)*(∑e,if hub e=u then w e else 0)-η*s*n|≤
      (S.card:ℝ)*err+η*countErr := by
  have hsum:|(∑v∈S,hypergraphWeightedDegree R w v)-(S.card:ℝ)*η|≤(S.card:ℝ)*err:=by
    have hh:|(∑v∈S,(hypergraphWeightedDegree R w v-η))|≤∑v∈S,|hypergraphWeightedDegree R w v-η|:=
      Finset.abs_sum_le_sum_abs (fun v=>hypergraphWeightedDegree R w v-η) S
    have hb:(∑v∈S,|hypergraphWeightedDegree R w v-η|)≤∑v∈S,err:=
      Finset.sum_le_sum (fun v hv=>hdeg v hv)
    simp only [Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul] at hh hb
    exact hh.trans hb
  rw [resource_hub_test_mass_identity R w hub u S r hS] at hsum
  have hc:|η*((S.card:ℝ)-s*n)|≤η*countErr:=by
    rw [abs_mul,abs_of_nonneg hη]
    exact mul_le_mul_of_nonneg_left hcount hη
  have htri:=abs_add_le
    ((r:ℝ)*(∑e,if hub e=u then w e else 0)-(S.card:ℝ)*η)
    (η*((S.card:ℝ)-s*n))
  have heq:(r:ℝ)*(∑e,if hub e=u then w e else 0)-η*s*n =
      ((r:ℝ)*(∑e,if hub e=u then w e else 0)-(S.card:ℝ)*η)+η*((S.card:ℝ)-s*n):=by ring
  rw [heq]
  linarith
end Oberwolfach
