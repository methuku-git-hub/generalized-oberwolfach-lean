module

public import Oberwolfach.HypergraphLineGraph

@[expose] public section

/-! An independent set in a line-graph neighbourhood has at most as many
vertices as the corresponding hyperedge has resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem hypergraphLineGraph_independent_neighbours
    {V E : Type*} (R : E → Finset V) (e : E) (S : Finset E)
    (hN : ∀ f∈S,(hypergraphLineGraph R).Adj e f)
    (hI : ∀ f∈S,∀ g∈S,f≠g → ¬(hypergraphLineGraph R).Adj f g) :
    S.card≤(R e).card := by
  classical
  have hex (f : S) : ∃ v,v∈R e ∧ v∈R f.val :=
    Finset.not_disjoint_iff.mp (hN f.val f.property).2
  let a : S → R e := fun f=>⟨Classical.choose (hex f),(Classical.choose_spec (hex f)).1⟩
  have ha (f : S) : (a f).val∈R f.val := (Classical.choose_spec (hex f)).2
  have hinj : Function.Injective a := by
    intro f g he
    apply Subtype.ext
    by_contra hne
    apply hI f.val f.property g.val g.property hne
    refine ⟨hne,?_⟩
    intro hd
    exact Finset.disjoint_left.mp hd (ha f) ((congrArg Subtype.val he).symm ▸ ha g)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective a hinj

end Oberwolfach
