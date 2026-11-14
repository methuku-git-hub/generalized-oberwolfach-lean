module

public import Oberwolfach.OrderedCycleFirstEdgeExists
public import Oberwolfach.RegularCycleIsomorphism

@[expose] public section
/-! A two-factor component admits a cyclic ordering starting with either
chosen direction of any of its edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

private theorem cycle_iso_first_edges_transport
    {A:Type} (G:SimpleGraph A) (n m:ℕ) (hn:1<n) (hm:1<m) (h:n=m)
    (e:SimpleGraph.cycleGraph m ≃g G) (a b:A)
    (he0:e ⟨0,by omega⟩=a) (he1:e ⟨1,by omega⟩=b):
    ∃e':SimpleGraph.cycleGraph n ≃g G,e' ⟨0,by omega⟩=a ∧ e' ⟨1,by omega⟩=b:=by
  subst m
  exact ⟨e,he0,he1⟩

theorem component_cycle_iso_with_first_edge
    {X:Type} [Fintype X] [DecidableEq X] (G:SimpleGraph X) (hG:G.IsRegularOfDegree 2)
    (C:G.ConnectedComponent) (a b:C) (hab:G.Adj a.val b.val):
    ∃ e:SimpleGraph.cycleGraph (Fintype.card C) ≃g C.toSimpleGraph,
      e ⟨0,by have h:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1;omega⟩=a ∧
      e ⟨1,by have h:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1;omega⟩=b:=by
  classical
  have h3:3≤Fintype.card C:=(component_regular_two_cycle_iso G hG C).1
  let m:=Fintype.card C-2
  have hN:Fintype.card C=m+2:=by dsimp [m];omega
  obtain ⟨e₀⟩:Nonempty (SimpleGraph.cycleGraph (m+2) ≃g C.toSimpleGraph):=by
    have hh:=(component_regular_two_cycle_iso G hG C).2
    rw [hN] at hh
    exact hh
  let f:Fin (m+2)↪C:=e₀.toEquiv.toEmbedding
  have hmap:(SimpleGraph.cycleGraph (m+2)).map f=C.toSimpleGraph:=by
    ext x y
    obtain ⟨x,rfl⟩:=e₀.surjective x
    obtain ⟨y,rfl⟩:=e₀.surjective y
    change ((SimpleGraph.cycleGraph (m+2)).map f).Adj (f x) (f y) ↔ C.toSimpleGraph.Adj (e₀ x) (e₀ y)
    rw [SimpleGraph.map_adj_apply]
    exact (e₀.map_adj_iff (v:=x) (w:=y)).symm
  have hab':((SimpleGraph.cycleGraph (m+2)).map f).Adj a b:=by
    rw [hmap]
    exact hab
  obtain ⟨g,hgmap,hg0,hg1⟩:=ordered_cycle_representation_first_edge_exists m f a b hab'
  rw [hmap] at hgmap
  have hcard:Fintype.card (Fin (m+2))=Fintype.card C:=by simp [hN]
  have hbij:Function.Bijective g:=(Fintype.bijective_iff_injective_and_card g).2 ⟨g.injective,hcard⟩
  let E:Fin (m+2)≃C:=Equiv.ofBijective g hbij
  let e:SimpleGraph.cycleGraph (m+2) ≃g C.toSimpleGraph:={
    toEquiv:=E
    map_rel_iff':=by
      intro x y
      rw [←hgmap]
      exact SimpleGraph.map_adj_apply }
  have he0:e 0=a:=hg0
  have he1:e 1=b:=hg1
  exact cycle_iso_first_edges_transport C.toSimpleGraph (Fintype.card C) (m+2) (by omega) (by omega) hN e a b
    (by simpa using he0) (by simpa using he1)
end Oberwolfach
