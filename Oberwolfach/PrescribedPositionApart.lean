module

public import Oberwolfach.PrescribedPositionSelectionNodup
public import Oberwolfach.PrescribedFamilyArcUniqueness

@[expose] public section
/-! The greedy position separation is symmetric and excludes all cross
adjacencies between chosen pieces. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_singles_apart_symm (Q:SimpleGraph X) (x y:X):
    prescribedSinglesApart Q x y→prescribedSinglesApart Q y x := by
  intro h
  simp only [prescribedSinglesApart,prescribedClosedNeighbourhood,Finset.mem_insert,
    SimpleGraph.mem_neighborFinset,not_or] at h ⊢
  exact ⟨Ne.symm h.1,fun hxy=>h.2 hxy.symm⟩

theorem prescribed_pairs_apart_symm (Q:SimpleGraph X) (e f:X×X):
    prescribedPairsApart Q e f→prescribedPairsApart Q f e := by
  intro h
  have h11:prescribedSinglesApart Q e.1 f.1:=fun hh=>h.1 (Finset.mem_union_left _ hh)
  have h21:prescribedSinglesApart Q e.2 f.1:=fun hh=>h.1 (Finset.mem_union_right _ hh)
  have h12:prescribedSinglesApart Q e.1 f.2:=fun hh=>h.2 (Finset.mem_union_left _ hh)
  have h22:prescribedSinglesApart Q e.2 f.2:=fun hh=>h.2 (Finset.mem_union_right _ hh)
  constructor
  · simp only [prescribedPairClosed,Finset.mem_union,not_or]
    exact ⟨prescribed_singles_apart_symm Q _ _ h11,prescribed_singles_apart_symm Q _ _ h12⟩
  · simp only [prescribedPairClosed,Finset.mem_union,not_or]
    exact ⟨prescribed_singles_apart_symm Q _ _ h21,prescribed_singles_apart_symm Q _ _ h22⟩

theorem prescribed_pairs_apart_no_adj (Q:SimpleGraph X) (e f:X×X)
    (h:prescribedPairsApart Q e f):
    ∀ x∈prescribedPairVertices e,∀ y∈prescribedPairVertices f,¬Q.Adj x y := by
  intro x hx y hy hxy
  simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with hx|hx <;> rcases hy with hy|hy <;> subst x <;> subst y
  · exact h.1 (Finset.mem_union_left _ (by simp [prescribedClosedNeighbourhood,hxy]))
  · exact h.2 (Finset.mem_union_left _ (by simp [prescribedClosedNeighbourhood,hxy]))
  · exact h.1 (Finset.mem_union_right _ (by simp [prescribedClosedNeighbourhood,hxy]))
  · exact h.2 (Finset.mem_union_right _ (by simp [prescribedClosedNeighbourhood,hxy]))

theorem prescribed_pair_single_no_adj (Q:SimpleGraph X) (e:X×X) (v:X)
    (h:v∉prescribedPairClosed Q e):∀ x∈prescribedPairVertices e,¬Q.Adj x v := by
  intro x hx hxy
  simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx <;> subst x
  · exact h (Finset.mem_union_left _ (by simp [prescribedClosedNeighbourhood,hxy]))
  · exact h (Finset.mem_union_right _ (by simp [prescribedClosedNeighbourhood,hxy]))
end Oberwolfach
