module

public import Oberwolfach.OrdinaryTriangleBufferedEndpointConstructedReservoirBundleCapped

@[expose] public section
/-! Derive the matching/reservoir host inputs from the original regular host,
using the actual permutation conflict graph as the forbidden graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_regular_triangle_matching_host_inputs
    (n D d:ℕ) (hn:0<n) (P:SimpleGraph (Fin n)) (hreg:P.IsRegularOfDegree D)
    (π:Equiv.Perm (Fin n)) (θ α εsample:ℝ)
    (hθ:1/2≤θ) (hcycle:cycleThreshold 3≤θ) (hα:0<α) (hε:0≤εsample)
    (hdegree:(θ+α)*(n:ℝ)≤D):
    (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧
    (∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤2*((3*d:ℕ):ℝ)) ∧
    (∀v,(cycleThreshold 3+α)*n≤(P.degree v:ℝ)) ∧
    (∀v,|(P.degree v:ℝ)-D|≤εsample*n) :=by
  let v:Fin n:=⟨0,hn⟩
  have hDn:D≤n:=by
    have hh:=Finset.card_le_univ (P.neighborFinset v)
    simpa [SimpleGraph.card_neighborFinset_eq_degree,hreg v] using hh
  have hDreal:(D:ℝ)≤n:=by exact_mod_cast hDn
  have hn0:0≤(n:ℝ):=by positivity
  have hθ':(1/2:ℝ)≤θ+α:=by linarith
  have hDlo:(n:ℝ)/2≤D:=by
    have hh:=mul_le_mul_of_nonneg_right hθ' hn0
    nlinarith only [hh,hdegree]
  have hF:∀v,((permutationConflictGraph π (3*d)).degree v:ℝ)≤2*((3*d:ℕ):ℝ):=by
    intro x
    have hh:=permutationConflictGraph_degree_le π (3*d) x
    exact_mod_cast hh
  refine ⟨hDlo,by nlinarith,hF,?_,?_⟩
  · intro x
    have hh:=mul_le_mul_of_nonneg_right (show cycleThreshold 3+α≤θ+α by linarith) hn0
    rw [hreg x]
    exact hh.trans hdegree
  · intro x
    rw [hreg x]
    simp only [sub_self,abs_zero]
    positivity
end Oberwolfach
