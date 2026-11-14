module

public import Oberwolfach.PrescribedPartialEmbedding

@[expose] public section
/-! Mapped source edges whose endpoints have been assigned lie in the image
of the induced source graph. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {X V:Type} [Fintype X] [Fintype V] [DecidableEq X] [DecidableEq V]

theorem prescribed_source_edges_image_contained (Q:SimpleGraph X) (A:Finset X) (f:X→V)
    (hinj:Set.InjOn f A) (T:Finset (Sym2 X)) (hsub:T⊆Q.edgeFinset)
    (hends:∀ e∈T,∀ x∈e.toFinset,x∈A):
    T.image (Sym2.map f) ⊆
      ((Q.induce (↑A:Set X)).map (prescribedPartialEmbedding A f hinj)).edgeFinset := by
  intro target htarget
  obtain ⟨edge,hsource,rfl⟩:=Finset.mem_image.mp htarget
  induction edge using Sym2.inductionOn with
  | _ x y =>
    have hx:x∈A:=hends _ hsource x (by simp)
    have hy:y∈A:=hends _ hsource y (by simp)
    have hQ:Q.Adj x y:=by
      have hh:=hsub hsource
      simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hh
    simp only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,Sym2.map_mk]
    change ((Q.induce (↑A:Set X)).map (prescribedPartialEmbedding A f hinj)).Adj (f x) (f y)
    apply (SimpleGraph.map_adj (prescribedPartialEmbedding A f hinj) _ _ _).mpr
    exact ⟨⟨x,hx⟩,⟨y,hy⟩,hQ,rfl,rfl⟩
end Oberwolfach
