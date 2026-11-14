module

public import Oberwolfach.PrescribedPositions

@[expose] public section
/-! An oriented graph and its underlying simple graph have the same number
of arcs and edges. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X:Type} [Fintype X] [DecidableEq X]

def prescribedArcFinset (D:X→X→Prop):Finset (X×X):=
  Finset.univ.filter (fun e=>D e.1 e.2)

theorem prescribed_arc_count_eq_edge_count (Q:SimpleGraph X) (D:X→X→Prop)
    (hrep:∀x y,Q.Adj x y→D x y ∨ D y x)
    (hDQ:∀x y,D x y→Q.Adj x y) (horiented:∀x y,D x y→¬D y x):
    (prescribedArcFinset D).card=Q.edgeFinset.card := by
  classical
  apply Finset.card_bij (fun e _=>s(e.1,e.2))
  · intro e he
    have h:D e.1 e.2:=(Finset.mem_filter.mp he).2
    simpa [SimpleGraph.mem_edgeFinset] using hDQ e.1 e.2 h
  · intro e he f hf heq
    rcases Sym2.mk_eq_mk_iff.mp heq with h|h
    · exact h
    · have heD:D e.1 e.2:=(Finset.mem_filter.mp he).2
      have hfD:D f.1 f.2:=(Finset.mem_filter.mp hf).2
      have hrev:D e.2 e.1:=by simpa [h] using hfD
      exact False.elim (horiented e.1 e.2 heD hrev)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy:Q.Adj x y:=by simpa [SimpleGraph.mem_edgeFinset] using he
      rcases hrep x y hxy with hd|hd
      · refine ⟨(x,y),?_,rfl⟩
        simp [prescribedArcFinset,hd]
      · refine ⟨(y,x),?_,?_⟩
        · simp [prescribedArcFinset,hd]
        · exact Sym2.eq_swap
theorem prescribed_positions_with_arc_count {V:Type} [Fintype V] [DecidableEq V]
    (Q:SimpleGraph X) (D:X→X→Prop)
    (hdeg:∀x,Q.degree x≤2) (hrep:∀x y,Q.Adj x y→D x y ∨ D y x)
    (hDQ:∀x y,D x y→Q.Adj x y) (horiented:∀x y,D x y→¬D y x)
    (A:Finset X) (hA:∀x∈A,∀y∈A,¬Q.Adj x y) (f:X→V) (hinj:Set.InjOn f (↑A:Set X))
    (M:Finset (V×V)) (hM:IsPrescribedOrientedMatching M) (Z:Finset V)
    (hOldM:Disjoint (A.image f) (prescribedMatchingEndpoints M))
    (hOldZ:Disjoint (A.image f) Z) (hMZ:Disjoint (prescribedMatchingEndpoints M) Z)
    (harc:Fintype.card X≤(prescribedArcFinset D).card+A.card)
    (hsize:8*A.card+8*M.card+4*Z.card+10≤Fintype.card X):
    ∃ (B:Finset X) (g:X→V),A⊆B ∧ Set.InjOn g (↑B:Set X) ∧ (∀x∈A,g x=f x) ∧
      B.image g=A.image f∪prescribedMatchingEndpoints M∪Z ∧
      (prescribedInducedArcs D B).image (Prod.map g g)=M := by
  apply prescribed_positions Q D hdeg hrep hDQ horiented A hA f hinj M hM Z hOldM hOldZ hMZ _ hsize
  simpa [prescribed_arc_count_eq_edge_count Q D hrep hDQ horiented] using harc
end Oberwolfach
