module

public import Oberwolfach.ActualReservedOrdinarySpokeLabels

@[expose] public section
/-! The matching assignment can avoid the actual reserved ordinary spokes
using their total number as a uniform endpoint-loss bound. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

theorem actual_reserved_spoke_matching_lists
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop) (S:Sym2 V→Finset I):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let L:=reservedSpokeMatchingList S A;
    (∀e,L e⊆S e) ∧
    (∀e v,v∈e.toFinset→∀i∈L e,v∉A i) ∧
    (∀e,(S e).card≤(L e).card+2*C.card) ∧
    (∀v i,Sum.inr (v,i)∈C→Hold false v i→v∈A i) :=by
  intro A L
  have hA:∀v,((Finset.univ:Finset I).filter (fun i=>v∈A i)).card≤C.card:=
    actual_reserved_ordinary_spoke_labels_incidence C Hold
  have hh:=reserved_spoke_matching_lists S A C.card hA
  refine ⟨hh.1,hh.2.1,hh.2.2,?_⟩
  intro v i hC hHold
  exact (actual_reserved_ordinary_spoke_labels_mem C Hold i v).mpr ⟨hC,hHold⟩
end Oberwolfach
