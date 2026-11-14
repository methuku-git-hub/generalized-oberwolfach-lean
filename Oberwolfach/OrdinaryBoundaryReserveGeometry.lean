module

public import Oberwolfach.OrdinaryBoundaryGraph

@[expose] public section
/-! Retained boundary edges lie in the actual host and avoid the protected
inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_reserve_geometry
    (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U) (σ:Sym2 (V⊕U)→Bool):
    let G:=retainedGraph (ordinaryBoundaryGraph Q H I J) σ;
    (G.comap Sum.inl)≤Q\spanningRestriction Q I ∧
    (∀v u,G.Adj (Sum.inl v) (Sum.inr u)→H v u∧¬(v∈I∧u∈J)):=by
  intro G
  have hbase (x y:V⊕U) (h:G.Adj x y):
      (ordinaryPhysicalGraph Q H).Adj x y ∧
        ((x∉ordinaryInnerVertices I J ∧ y∈ordinaryInnerVertices I J) ∨
         (y∉ordinaryInnerVertices I J ∧ x∈ordinaryInnerVertices I J)):=by
    exact (ordinaryBoundaryGraph_adj Q H I J x y).mp h.1
  constructor
  · intro v w hvw
    have hh:=hbase (Sum.inl v) (Sum.inl w) hvw
    have hQ:Q.Adj v w:=hh.1
    refine ⟨hQ,?_⟩
    intro hi
    have hv: v∈I:=(spanningRestriction_adj Q I v w).mp hi |>.2.1
    have hw: w∈I:=(spanningRestriction_adj Q I v w).mp hi |>.2.2
    have hvi:Sum.inl v∈ordinaryInnerVertices I J:=(ordinaryInnerVertices_left I J v).mpr hv
    have hwi:Sum.inl w∈ordinaryInnerVertices I J:=(ordinaryInnerVertices_left I J w).mpr hw
    rcases hh.2 with h|h
    · exact h.1 hvi
    · exact h.1 hwi
  · intro v u hvu
    have hh:=hbase (Sum.inl v) (Sum.inr u) hvu
    refine ⟨hh.1,?_⟩
    rintro ⟨hv,hu⟩
    have hvi:Sum.inl v∈ordinaryInnerVertices I J:=(ordinaryInnerVertices_left I J v).mpr hv
    have hui:Sum.inr u∈ordinaryInnerVertices I J:=(ordinaryInnerVertices_right I J u).mpr hu
    rcases hh.2 with h|h
    · exact h.1 hvi
    · exact h.1 hui
end Oberwolfach
