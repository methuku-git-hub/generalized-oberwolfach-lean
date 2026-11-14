module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section
/-! Excluding the reserved spoke labels at both endpoints removes at most
the two endpoint incidence bounds from each matching list. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def reservedSpokeMatchingList {V I:Type} [DecidableEq V] [DecidableEq I]
    (S:Sym2 V→Finset I) (A:I→Finset V) (e:Sym2 V):Finset I:=
  (S e).filter (fun i=>∀v∈e.toFinset,v∉A i)

theorem reserved_spoke_matching_lists {V I:Type} [Fintype I] [DecidableEq V] [DecidableEq I]
    (S:Sym2 V→Finset I) (A:I→Finset V) (b:ℕ)
    (hA:∀v,(Finset.univ.filter (fun i=>v∈A i)).card≤b):
    let L:=reservedSpokeMatchingList S A;
    (∀e,L e⊆S e) ∧ (∀e v,v∈e.toFinset→∀i∈L e,v∉A i) ∧
    (∀e,(S e).card≤(L e).card+2*b) :=by
  intro L
  have hsub:∀e,L e⊆S e:=by intro e i hi;exact (Finset.mem_filter.mp hi).1
  have hgood:∀e v,v∈e.toFinset→∀i∈L e,v∉A i:=by
    intro e v hv i hi
    exact (Finset.mem_filter.mp hi).2 v hv
  refine ⟨hsub,hgood,?_⟩
  intro e
  let Bad:=fun v:V=>(Finset.univ:Finset I).filter (fun i=>v∈A i)
  have hcover:S e⊆L e∪e.toFinset.biUnion Bad:=by
    intro i hi
    by_cases hg:∀v∈e.toFinset,v∉A i
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi,hg⟩)
    · push_neg at hg
      obtain ⟨v,hv,hvi⟩:=hg
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvi⟩⟩)
  have hEnds:e.toFinset.card≤2:=by rw [Sym2.card_toFinset];split_ifs <;> omega
  have hBad:(e.toFinset.biUnion Bad).card≤e.toFinset.card*b:=
    Finset.card_biUnion_le_card_mul _ _ _ (fun v _=>hA v)
  have hc:=(Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  nlinarith
end Oberwolfach
