module

public import Oberwolfach.PrescribedPositionGreedySelection

@[expose] public section
/-! The vertices selected for source matching edges and isolated positions
are all distinct. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

def prescribedPairVertices (e:X×X):List X:=[e.1,e.2]

theorem prescribed_pairs_apart_disjoint (Q:SimpleGraph X) (e f:X×X)
    (h:prescribedPairsApart Q e f):List.Disjoint (prescribedPairVertices e) (prescribedPairVertices f) := by
  apply List.disjoint_left.mpr
  intro x hx hy
  simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hx hy
  rcases hx with hx|hx <;> rcases hy with hy|hy <;> subst x
  · exact h.1 (by simp [prescribedPairClosed,prescribedClosedNeighbourhood,←hy])
  · exact h.2 (by simp [prescribedPairClosed,prescribedClosedNeighbourhood,←hy])
  · exact h.1 (by simp [prescribedPairClosed,prescribedClosedNeighbourhood,←hy])
  · exact h.2 (by simp [prescribedPairClosed,prescribedClosedNeighbourhood,←hy])

theorem prescribed_pair_vertices_nodup (Q:SimpleGraph X) (es:List (X×X))
    (hE:∀e∈es,Q.Adj e.1 e.2) (hpair:es.Pairwise (prescribedPairsApart Q)):
    (es.flatMap prescribedPairVertices).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    have hne:e.1≠e.2:=Q.ne_of_adj (hE e he)
    simp [prescribedPairVertices,hne]
  · apply hpair.imp
    intro e f h
    exact prescribed_pairs_apart_disjoint Q e f h

theorem prescribed_singles_nodup (Q:SimpleGraph X) (vs:List X)
    (hpair:vs.Pairwise (prescribedSinglesApart Q)):vs.Nodup := by
  apply hpair.imp
  intro x y h hxy
  subst y
  exact h (by simp [prescribedSinglesApart,prescribedClosedNeighbourhood])

theorem prescribed_selected_vertices_nodup (Q:SimpleGraph X) (es:List (X×X)) (vs:List X)
    (hE:∀e∈es,Q.Adj e.1 e.2) (hpair:es.Pairwise (prescribedPairsApart Q))
    (hsingle:vs.Pairwise (prescribedSinglesApart Q))
    (hcross:∀ e∈es,∀v∈vs,v∉prescribedPairClosed Q e):
    (es.flatMap prescribedPairVertices++vs).Nodup := by
  apply List.nodup_append'.mpr
  refine ⟨prescribed_pair_vertices_nodup Q es hE hpair,prescribed_singles_nodup Q vs hsingle,?_⟩
  apply List.disjoint_left.mpr
  intro x hx hy
  obtain ⟨e,he,hx⟩:=List.mem_flatMap.mp hx
  simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx <;> subst x
  · exact hcross e he _ hy (by simp [prescribedPairClosed,prescribedClosedNeighbourhood])
  · exact hcross e he _ hy (by simp [prescribedPairClosed,prescribedClosedNeighbourhood])
end Oberwolfach
