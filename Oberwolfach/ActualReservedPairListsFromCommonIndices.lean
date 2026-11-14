module

public import Oberwolfach.ActualReservedSpokeMatchingLists

@[expose] public section
/-! Construct the manuscript's bad-edge list from the common outer labels,
remove the inner indices and the actual reserved spokes, and count the loss. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V I:Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def commonOuterPairIndices (Outer:I→Finset V) (e:Sym2 V):Finset I:=
  Finset.univ.filter (fun i=>∀v∈e.toFinset,v∈Outer i)

theorem common_outer_pair_indices_eq_intersection
    (Outer:I→Finset V) (x y:V):
    commonOuterPairIndices Outer s(x,y)=
      ((Finset.univ:Finset I).filter (fun i=>x∈Outer i))∩
      ((Finset.univ:Finset I).filter (fun i=>y∈Outer i)) :=by
  ext i
  simp [commonOuterPairIndices,Sym2.toFinset_mk_eq]

theorem actual_reserved_pair_lists_from_common_indices
    (C:Finset (Finset V⊕(V×I))) (Hold:Bool→V→I→Prop)
    (Outer:I→Finset V) (Inner:Finset I):
    let A:=actualReservedOrdinarySpokeLabels C Hold
    let S:=fun e=>commonOuterPairIndices Outer e\Inner
    let L:=reservedSpokeMatchingList S A;
    (∀e,Disjoint (S e) Inner) ∧
    (∀e i,i∈S e→∀v∈e.toFinset,v∈Outer i) ∧
    (∀e v,v∈e.toFinset→∀i∈L e,v∉A i) ∧
    (∀e,(commonOuterPairIndices Outer e).card≤(L e).card+Inner.card+2*C.card) :=by
  intro A S L
  have hL:=actual_reserved_spoke_matching_lists C Hold S
  refine ⟨?_,?_,hL.2.1,?_⟩
  · intro e
    apply Finset.disjoint_left.mpr
    intro i hi hInner
    exact (Finset.mem_sdiff.mp hi).2 hInner
  · intro e i hi v hv
    have him:i∈commonOuterPairIndices Outer e:=(Finset.mem_sdiff.mp hi).1
    exact (Finset.mem_filter.mp him).2 v hv
  · intro e
    have hcut:(commonOuterPairIndices Outer e).card≤(S e).card+Inner.card:=
      Finset.card_le_card_sdiff_add_card
    have hl:(S e).card≤(L e).card+2*C.card:=hL.2.2.1 e
    omega
theorem actual_outer_pair_lists_from_common_slack
    (C:Finset (Finset V⊕(V×I))) (Outer:I→Finset V) (Inner:Finset I) (K:SimpleGraph V) (α:ℝ)
    (hCommon:∀e∈K.edgeFinset,α*Fintype.card V+Inner.card+2*C.card≤
      ((commonOuterPairIndices Outer e).card:ℝ)):
    let S:=fun e=>commonOuterPairIndices Outer e\Inner;
    (∀e∈K.edgeFinset,Disjoint (S e) Inner) ∧
    (∀e∈K.edgeFinset,∀i∈S e,∀v∈e.toFinset,v∈Outer i) ∧
    (∀e∈K.edgeFinset,α*Fintype.card V+2*C.card≤((S e).card:ℝ)) :=by
  intro S
  refine ⟨?_,?_,?_⟩
  · intro e he
    apply Finset.disjoint_left.mpr
    intro i hi hInner
    exact (Finset.mem_sdiff.mp hi).2 hInner
  · intro e he i hi v hv
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).2 v hv
  · intro e he
    have hcut:((commonOuterPairIndices Outer e).card:ℝ)≤(S e).card+Inner.card:=by
      exact_mod_cast (Finset.card_le_card_sdiff_add_card (s:=commonOuterPairIndices Outer e) (t:=Inner))
    linarith [hCommon e he]
theorem actual_common_outer_pair_slack_from_codegrees
    (C:Finset (Finset V⊕(V×I))) (Outer:I→Finset V) (Inner:Finset I) (K:SimpleGraph V) (α:ℝ)
    (hPairs:∀x y,x≠y→2*α*Fintype.card V≤
      ((((Finset.univ:Finset I).filter (fun i=>x∈Outer i))∩
        ((Finset.univ:Finset I).filter (fun i=>y∈Outer i))).card:ℝ))
    (hLoss:(Inner.card:ℝ)+2*C.card≤α*Fintype.card V):
    ∀e∈K.edgeFinset,α*Fintype.card V+Inner.card+2*C.card≤
      ((commonOuterPairIndices Outer e).card:ℝ) :=by
  intro e he
  induction e using Sym2.ind with
  | _ x y =>
    have hxy:K.Adj x y:=by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he
    rw [common_outer_pair_indices_eq_intersection]
    linarith [hPairs x y hxy.ne]
end Oberwolfach
