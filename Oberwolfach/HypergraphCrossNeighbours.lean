module

public import Oberwolfach.HypergraphLineGraph

@[expose] public section

/-! The number of neighbours in another resource clique is small when
the root edge does not contain that resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraph_neighbours_in_other_clique
    {V E : Type*} [Fintype E] (R : E → Finset V) {k B : ℕ}
    (hsize : ∀ e,(R e).card≤k)
    (hcodeg : ∀ v w,v≠w → (Finset.univ.filter (fun e=>v∈R e ∧ w∈R e)).card≤B)
    (e : E) (z : V) (hz : z∉R e) (T : Finset E) (hT : ∀ f∈T,z∈R f) :
    (T.filter (fun f=>(hypergraphLineGraph R).Adj e f)).card≤k*B := by
  classical
  let N := fun v=>Finset.univ.filter (fun f=>v∈R f ∧ z∈R f)
  have hsub : T.filter (fun f=>(hypergraphLineGraph R).Adj e f)⊆(R e).biUnion N := by
    intro f hf
    obtain ⟨hfT,_,hdis⟩ := Finset.mem_filter.mp hf
    obtain ⟨v,hve,hvf⟩ := Finset.not_disjoint_iff.mp hdis
    exact Finset.mem_biUnion.mpr ⟨v,hve,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hvf,hT f hfT⟩⟩
  calc
    _ ≤ ((R e).biUnion N).card := Finset.card_le_card hsub
    _ ≤ (R e).card*B := Finset.card_biUnion_le_card_mul _ _ _ (fun v hv=>
      hcodeg v z (fun he=>hz (he ▸ hv)))
    _ ≤ _ := Nat.mul_le_mul_right _ (hsize e)

end Oberwolfach
