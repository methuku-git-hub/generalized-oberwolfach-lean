module

public import Oberwolfach.OrdinaryRootResourceCardinality
public import Oberwolfach.OrdinaryResourceSubgraphs

@[expose] public section
/-! The physical rim of a bounded resource reservoir is a bounded protected
graph; root avoidance excludes its edges from the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reservoir_resource_card_bound
    (A:Finset (Sym2 V⊕(V×U))) (a b:ℕ)
    (hrow:(ordinaryResourceRows A).card≤a) (hhub:(ordinaryResourceHubs A).card≤b):
    A.card≤a*a+a*b:=by
  have hsub:A⊆ordinaryRootResources (ordinaryResourceRows A) (ordinaryResourceHubs A):=
    ordinaryRootResources_contains A _ _ (Finset.Subset.refl _) (Finset.Subset.refl _)
  have h₁:=Finset.card_le_card hsub
  have h₂:=ordinary_root_resources_card_le (ordinaryResourceRows A) (ordinaryResourceHubs A)
  exact h₁.trans (h₂.trans (Nat.add_le_add (Nat.mul_le_mul hrow hrow) (Nat.mul_le_mul hrow hhub)))

theorem ordinary_reservoir_rim_edge_card_le
    (P:SimpleGraph V) (A:Finset (Sym2 V⊕(V×U))):
    (ordinaryResourceRim P A).edgeFinset.card≤A.card:=by
  have hsub:((ordinaryResourceRim P A).edgeFinset.image Sum.inl)⊆A:=by
    intro e he
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp he
    induction x using Sym2.inductionOn with
    | _ v w=>
      have hh:(ordinaryResourceRim P A).Adj v w:=SimpleGraph.mem_edgeFinset.mp hx
      exact hh.2
  have hcard:=Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ Sum.inl_injective] at hcard
  exact hcard

theorem ordinary_reservoir_protected_graph
    (P S₀:SimpleGraph V) (A:Finset (Sym2 V⊕(V×U))) (Inner:Finset V) (B:Finset U)
    (a b:ℕ) (hPS:P≤S₀) (hrow:(ordinaryResourceRows A).card≤a)
    (hhub:(ordinaryResourceHubs A).card≤b) (hInner:Disjoint A (ordinaryRootResources Inner B)):
    let R:=ordinaryResourceRim P A;
    R≤S₀ ∧ R.edgeFinset.card≤a*a+a*b ∧
      (∀v∈Inner,∀w∈Inner,¬R.Adj v w):=by
  intro R
  refine ⟨(fun _ _ h=>hPS h.1),?_,?_⟩
  · exact (ordinary_reservoir_rim_edge_card_le P A).trans (ordinary_reservoir_resource_card_bound A a b hrow hhub)
  · intro v hv w hw he
    exact Finset.disjoint_left.mp hInner he.2 (ordinaryRootResources_rim Inner B v w hv hw)
end Oberwolfach
