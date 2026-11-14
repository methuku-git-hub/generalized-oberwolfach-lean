module

public import Oberwolfach.PrescribedPositionOriginalSelection
public import Oberwolfach.PrescribedPositionInducedEdges

@[expose] public section
/-! Adding the selected source positions to the original independent set
induces exactly the selected oriented arcs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

theorem prescribed_selected_induced_arcs (Q:SimpleGraph X) (D:X→X→Prop) (A:Finset X)
    (hDQ:∀x y,D x y→Q.Adj x y) (horiented:∀x y,D x y→¬D y x)
    (hA:∀x∈A,∀y∈A,¬Q.Adj x y)
    (es:List (X×X)) (vs:List X)
    (hE:∀e∈es,D e.1 e.2 ∧ e.1∉prescribedClosedNeighbourhoods Q A ∧ e.2∉prescribedClosedNeighbourhoods Q A)
    (hpair:es.Pairwise (prescribedPairsApart Q))
    (hvs:∀v∈vs,v∉prescribedClosedNeighbourhoods Q A)
    (hcross:∀ e∈es,∀v∈vs,v∉prescribedPairClosed Q e)
    (hsingle:vs.Pairwise (prescribedSinglesApart Q)):
    ∀ x y,D x y→x∈A∪(es.flatMap prescribedPairVertices++vs).toFinset→
      y∈A∪(es.flatMap prescribedPairVertices++vs).toFinset→(x,y)∈es := by
  intro x y hxy hx hy
  have hx':x∈A ∨ x∈es.flatMap prescribedPairVertices++vs:=by
    rcases Finset.mem_union.mp hx with hx|hx
    · exact Or.inl hx
    · exact Or.inr (List.mem_toFinset.mp hx)
  have hy':y∈A ∨ y∈es.flatMap prescribedPairVertices++vs:=by
    rcases Finset.mem_union.mp hy with hy|hy
    · exact Or.inl hy
    · exact Or.inr (List.mem_toFinset.mp hy)
  have hout:∀v∈es.flatMap prescribedPairVertices++vs,v∉prescribedClosedNeighbourhoods Q A:=by
    intro v hv
    rcases List.mem_append.mp hv with hv|hv
    · obtain ⟨e,he,hv⟩:=List.mem_flatMap.mp hv
      simp only [prescribedPairVertices,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with hv|hv
      · subst v;exact (hE e he).2.1
      · subst v;exact (hE e he).2.2
    · exact hvs v hv
  rcases hx' with hx|hx <;> rcases hy' with hy|hy
  · exact (hA x hx y hy (hDQ x y hxy)).elim
  · exact ((prescribed_outside_closed_neighbourhood Q A y (hout y hy)).2 x hx (hDQ x y hxy)).elim
  · exact ((prescribed_outside_closed_neighbourhood Q A x (hout x hx)).2 y hy (hDQ x y hxy).symm).elim
  · obtain ⟨e,he,hpos⟩:=prescribed_selected_induced_edge Q es vs hpair hsingle hcross x y hx hy (hDQ x y hxy)
    rcases hpos with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact he
    · exact (horiented e.1 e.2 (hE e he).1 hxy).elim
end Oberwolfach
