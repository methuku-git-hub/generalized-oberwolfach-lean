module

public import Oberwolfach.HypergraphWeightMoments

@[expose] public section
/-! The total fixed weight of candidates in a hub class can be read from
their weighted degrees on the actual retained spoke set. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E U:Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq U]

theorem resource_subset_weighted_degree_sum
    (R:E→Finset V) (w:E→ℝ) (S:Finset V):
    (∑v∈S,hypergraphWeightedDegree R w v)=∑e,((R e∩S).card:ℝ)*w e := by
  unfold hypergraphWeightedDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [←Finset.sum_filter]
  have he:S.filter (fun v=>v∈R e)=R e∩S := by ext v;simp [and_comm]
  rw [he,Finset.sum_const,nsmul_eq_mul]

theorem resource_hub_test_mass_identity
    (R:E→Finset V) (w:E→ℝ) (hub:E→U) (u:U) (S:Finset V) (r:ℕ)
    (hS:∀e,(R e∩S).card=if hub e=u then r else 0):
    (∑v∈S,hypergraphWeightedDegree R w v)=(r:ℝ)*∑e,if hub e=u then w e else 0 := by
  rw [resource_subset_weighted_degree_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [hS e]
  split_ifs <;> simp

theorem resource_hub_test_mass_lower
    (R:E→Finset V) (w:E→ℝ) (hub:E→U) (u:U) (S:Finset V) (r:ℕ)
    (hr:0<r) (hS:∀e,(R e∩S).card=if hub e=u then r else 0)
    (a:ℝ) (hdeg:∀v∈S,a≤hypergraphWeightedDegree R w v):
    a*(S.card:ℝ)/(r:ℝ)≤∑e,if hub e=u then w e else 0 := by
  have hsum:∑v∈S,a≤∑v∈S,hypergraphWeightedDegree R w v:=
    Finset.sum_le_sum (fun v hv=>hdeg v hv)
  simp only [Finset.sum_const,nsmul_eq_mul] at hsum
  rw [resource_hub_test_mass_identity R w hub u S r hS] at hsum
  have hrR:(0:ℝ)<r:=by exact_mod_cast hr
  apply (div_le_iff₀ hrR).2
  nlinarith
end Oberwolfach
