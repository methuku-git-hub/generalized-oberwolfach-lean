module

public import Oberwolfach.Definitions
public import Oberwolfach.PrescribedEmbeddingDisjointUpdate
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

@[expose] public section
/-! Spanning edge-disjoint two-factor images inside a regular host exhaust its
edges when the number of factors is half the host degree. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators

theorem regular_host_two_factor_edge_sets_exhaust {n q:ℕ}
    (G:SimpleGraph (Fin n)) (hG:G.IsRegularOfDegree (2*q))
    (E:Fin q→Finset (Sym2 (Fin n)))
    (hCard:∀i,(E i).card=n) (hsub:∀i,E i⊆G.edgeFinset)
    (hdis:PairwisePhysicalDisjoint E):
    Finset.univ.biUnion E=G.edgeFinset :=by
  have hsum:=G.sum_degrees_eq_twice_card_edges
  have hdegrees:(∑v,G.degree v)=n*(2*q):=by
    simp [show ∀v,G.degree v=2*q from hG,mul_comm]
  have hGcard:G.edgeFinset.card=q*n:=by nlinarith
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    exact hsub i hi
  · rw [Finset.card_biUnion (by intro i _ j _ hij;exact hdis i j hij),hGcard]
    simp [hCard,mul_comm]
end Oberwolfach
