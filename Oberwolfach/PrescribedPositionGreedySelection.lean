module

public import Oberwolfach.PrescribedPositionGreedyPairs
public import Oberwolfach.PrescribedPositionGreedySingles

@[expose] public section
/-! Select the source positions for matching edges and isolated images. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
open scoped BigOperators
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_position_greedy_selection (Q:SimpleGraph X) (D:X→X→Prop)
    (hdeg:∀ x,Q.degree x≤2) (hrep:∀x y,Q.Adj x y→D x y ∨ D y x)
    (S:Finset X) (m z:ℕ) (hE:2*S.card+8*m≤Q.edgeFinset.card)
    (hV:S.card+4*m+3*z≤Fintype.card X):
    ∃ (es:List (X×X)) (vs:List X),es.length=m ∧ vs.length=z ∧
      (∀ e∈es,D e.1 e.2 ∧ Q.Adj e.1 e.2 ∧ e.1∉S ∧ e.2∉S) ∧
      es.Pairwise (prescribedPairsApart Q) ∧ (∀ v∈vs,v∉S) ∧
      (∀ e∈es,∀ v∈vs,v∉prescribedPairClosed Q e) ∧
      vs.Pairwise (prescribedSinglesApart Q) := by
  obtain ⟨es,heslen,hes,hpair⟩:=prescribed_position_greedy_pairs Q D hdeg hrep m S hE
  let C:Finset X:=es.toFinset.biUnion (prescribedPairClosed Q)
  have hC:C.card≤4*m:=by
    calc
      C.card≤∑ e∈es.toFinset,(prescribedPairClosed Q e).card:=Finset.card_biUnion_le
      _≤∑ _e∈es.toFinset,4:=by
        apply Finset.sum_le_sum
        intro e he
        exact prescribed_edge_closed_neighbourhood_card Q hdeg e.1 e.2 (hes e (List.mem_toFinset.mp he)).2.1
      _=4*es.toFinset.card:=by simp [Nat.mul_comm]
      _≤4*es.length:=Nat.mul_le_mul_left 4 (List.toFinset_card_le es)
      _=4*m:=by rw [heslen]
  let T:=S∪C
  have hT:T.card≤S.card+4*m:=(Finset.card_union_le _ _).trans (Nat.add_le_add_left hC _)
  have hbudget:T.card+3*z≤Fintype.card X:=by omega
  obtain ⟨vs,hvslen,hvs,hvsPair⟩:=prescribed_position_greedy_singles Q hdeg z T hbudget
  refine ⟨es,vs,heslen,hvslen,hes,hpair,?_,?_,hvsPair⟩
  · intro v hv hs;exact hvs v hv (Finset.mem_union_left _ hs)
  · intro e he v hv hclosed
    have hvC:v∈C:=Finset.mem_biUnion.mpr ⟨e,List.mem_toFinset.mpr he,hclosed⟩
    exact hvs v hv (Finset.mem_union_right _ hvC)
end Oberwolfach
