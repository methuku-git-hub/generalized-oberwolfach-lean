module

public import Oberwolfach.ExtendingListGreedyChoice

@[expose] public section
/-! One-endpoint and free choices for the same prescribed-image embedding. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V:Type} [Fintype V] [DecidableEq V]

theorem extending_list_one_arc_choice (D:V→V→Prop) (L B:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (F:SimpleGraph V) (x:V) (forward:Bool)
    (hbudget:(B.card:ℝ)+F.degree x<β*Fintype.card V):
    ∃ z∈L,z∉B ∧ (if forward then D x z else D z x) ∧ ¬F.Adj x z := by
  let N:=if forward then directedOutNeighbours D x else directedInNeighbours D x
  let C:=N∩L
  let T:=B∪F.neighborFinset x
  have hlo:β*Fintype.card V≤(C.card:ℝ):=by
    cases forward with
    | false => exact (hext.2.2.1 x).2
    | true => exact (hext.2.2.1 x).1
  have hcard:(T.card:ℝ)≤(B.card:ℝ)+F.degree x:=by
    have hh:=Finset.card_union_le B (F.neighborFinset x)
    have hnat:T.card≤B.card+F.degree x:=by simpa [T,SimpleGraph.card_neighborFinset_eq_degree] using hh
    exact_mod_cast hnat
  have hnot:¬C⊆T:=by
    intro hsub
    have hh:C.card≤T.card:=Finset.card_le_card hsub
    have hhR:(C.card:ℝ)≤T.card:=by exact_mod_cast hh
    linarith
  obtain ⟨z,hzC,hzT⟩:=Finset.not_subset.mp hnot
  have hz:=Finset.mem_inter.mp hzC
  have hzB:z∉B:=fun h=>hzT (by simp [T,h])
  have hzF:¬F.Adj x z:=fun h=>hzT (by simp [T,h])
  refine ⟨z,hz.2,hzB,?_,hzF⟩
  cases forward <;> simpa [N,directedOutNeighbours,directedInNeighbours] using hz.1

theorem extending_list_free_choice (D:V→V→Prop) (L B:Finset V) (β:ℝ)
    (hext:IsExtendingList D L β) (hbudget:(B.card:ℝ)<β*Fintype.card V):
    ∃ z∈L,z∉B := by
  have hnot:¬L⊆B:=by
    intro hsub
    have hh:L.card≤B.card:=Finset.card_le_card hsub
    have hhR:(L.card:ℝ)≤B.card:=by exact_mod_cast hh
    linarith [hext.2.1]
  exact Finset.not_subset.mp hnot
end Oberwolfach
