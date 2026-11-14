module

public import Oberwolfach.DependentResidualDirectedHost
public import Oberwolfach.PrescribedPositionPairing

@[expose] public section
/-! A residual edge avoids all old edges if its prescribed matching edges
and its free directed edges each avoid them. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_dependent_residual_avoids_old_edges
    {I V:Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    {X:I→Type} [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]
    (pieces:∀i,List (PrescribedSourcePiece (X i))) (B:∀i,Finset (X i))
    (g Φ:∀i,X i→V) (M:I→Finset (V×V)) (Dfree:V→V→Prop)
    (hΦ:∀i x,x∈B i→Φ i x=g i x)
    (hM:∀i,(prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i)).image
      (Prod.map (g i) (g i))=M i)
    (hfree:∀i x y,prescribedDependentDigraph pieces i x y→
      (x∉B i ∨ y∉B i)→Dfree (Φ i x) (Φ i y))
    (Old:I→Finset (Sym2 V))
    (hMatchOld:∀i j,Disjoint (Old j) ((M i).image prescribedArcPhysical))
    (hFreeOld:∀i x y,Dfree x y→s(x,y)∉Old i):
    ∀i j,Disjoint (Old j) (((prescribedDependentGraph pieces i).edgeFinset).image (Sym2.map (Φ i))):=by
  intro i j
  have harc:∀x y,prescribedDependentDigraph pieces i x y→s(Φ i x,Φ i y)∉Old j:=by
    intro x y hxy
    by_cases hx:x∈B i
    · by_cases hy:y∈B i
      · have hsrc:(x,y)∈prescribedInducedArcs (prescribedDependentDigraph pieces i) (B i):=by
          simp [prescribedInducedArcs,hx,hy,hxy]
        have htarget:(g i x,g i y)∈M i:=by
          rw [←hM i]
          exact Finset.mem_image.mpr ⟨(x,y),hsrc,rfl⟩
        have hedge:s(Φ i x,Φ i y)∈(M i).image prescribedArcPhysical:=by
          rw [hΦ i x hx,hΦ i y hy]
          exact Finset.mem_image.mpr ⟨(g i x,g i y),htarget,rfl⟩
        intro hold
        exact Finset.disjoint_left.mp (hMatchOld i j) hold hedge
      · exact hFreeOld j _ _ (hfree i x y hxy (Or.inr hy))
    · exact hFreeOld j _ _ (hfree i x y hxy (Or.inl hx))
  apply Finset.disjoint_left.mpr
  intro target hold htarget
  obtain ⟨edge,hedge,rfl⟩:=Finset.mem_image.mp htarget
  induction edge using Sym2.ind with
  | _ x y =>
    have hxy:(prescribedDependentGraph pieces i).Adj x y:=by
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hedge
    change s(Φ i x,Φ i y)∈Old j at hold
    rcases prescribed_dependent_graph_edge_has_arc pieces i x y hxy with hh|hh
    · exact harc x y hh hold
    · exact harc y x hh (by simpa only [Sym2.eq_swap] using hold)
end Oberwolfach
