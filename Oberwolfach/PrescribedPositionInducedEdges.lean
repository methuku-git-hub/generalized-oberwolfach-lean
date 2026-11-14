module

public import Oberwolfach.PrescribedPositionApart

@[expose] public section
/-! Among the newly selected source positions, the only physical edges are
the selected matching edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_selected_induced_edge (Q:SimpleGraph X) (es:List (X×X)) (vs:List X)
    (hpair:es.Pairwise (prescribedPairsApart Q)) (hsingle:vs.Pairwise (prescribedSinglesApart Q))
    (hcross:∀ e∈es,∀ v∈vs,v∉prescribedPairClosed Q e)
    (x y:X) (hx:x∈es.flatMap prescribedPairVertices++vs)
    (hy:y∈es.flatMap prescribedPairVertices++vs) (hxy:Q.Adj x y):
    ∃ e∈es,(x=e.1 ∧ y=e.2) ∨ (x=e.2 ∧ y=e.1) := by
  rcases List.mem_append.mp hx with hx|hx <;> rcases List.mem_append.mp hy with hy|hy
  · obtain ⟨e,he,hxe⟩:=List.mem_flatMap.mp hx
    obtain ⟨f,hf,hyf⟩:=List.mem_flatMap.mp hy
    rcases prescribed_pairwise_rel_or_eq (prescribedPairsApart Q) (prescribed_pairs_apart_symm Q) es hpair e he f hf with heq|hapart
    · subst f
      simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hxe hyf
      rcases hxe with hxe|hxe <;> rcases hyf with hyf|hyf
      · subst x;subst y;exact (Q.irrefl hxy).elim
      · exact ⟨e,he,Or.inl ⟨hxe,hyf⟩⟩
      · exact ⟨e,he,Or.inr ⟨hxe,hyf⟩⟩
      · subst x;subst y;exact (Q.irrefl hxy).elim
    · exact (prescribed_pairs_apart_no_adj Q e f hapart x hxe y hyf hxy).elim
  · obtain ⟨e,he,hxe⟩:=List.mem_flatMap.mp hx
    exact (prescribed_pair_single_no_adj Q e y (hcross e he y hy) x hxe hxy).elim
  · obtain ⟨f,hf,hyf⟩:=List.mem_flatMap.mp hy
    exact (prescribed_pair_single_no_adj Q f x (hcross f hf x hx) y hyf hxy.symm).elim
  · rcases prescribed_pairwise_rel_or_eq (prescribedSinglesApart Q) (prescribed_singles_apart_symm Q) vs hsingle x hx y hy with heq|hapart
    · subst y;exact (Q.irrefl hxy).elim
    · exact (hapart (by simp [prescribedSinglesApart,prescribedClosedNeighbourhood,hxy])).elim
end Oberwolfach
