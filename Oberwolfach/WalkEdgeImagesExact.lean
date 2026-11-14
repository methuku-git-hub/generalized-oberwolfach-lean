module

public import Oberwolfach.ActualMatchedPieceDirectedArcs

@[expose] public section
/-! Equal-length walks with matching vertex images have exactly matching
physical edge images. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walk_edge_images_exact
    {X V:Type} [DecidableEq X] [DecidableEq V] (G:SimpleGraph X) (H:SimpleGraph V)
    {a b:X} {c d:V} (p:G.Walk a b) (q:H.Walk c d) (f:X→V)
    (hlen:q.length=p.length) (hmap:∀k,k≤p.length→f (p.getVert k)=q.getVert k):
    p.edges.toFinset.image (Sym2.map f)=q.edges.toFinset:=by
  ext edge
  constructor
  · intro he
    obtain ⟨e,he,heq⟩:=Finset.mem_image.mp he
    induction e using Sym2.ind with
    | _ x y =>
      obtain ⟨k,hk,hxy⟩:=(p.mk_mem_edges_iff_exists).mp (List.mem_toFinset.mp he)
      have ht:s((q.getVert k),(q.getVert (k+1)))=edge:=by
        rw [←hmap k (by omega),←hmap (k+1) (by omega)]
        have hh:=congrArg (Sym2.map f) hxy
        exact hh.trans heq
      apply List.mem_toFinset.mpr
      rw [←ht]
      exact (q.mk_mem_edges_iff_exists).mpr ⟨k,by omega,rfl⟩
  · intro he
    induction edge using Sym2.ind with
    | _ x y =>
      obtain ⟨k,hk,hxy⟩:=(q.mk_mem_edges_iff_exists).mp (List.mem_toFinset.mp he)
      apply Finset.mem_image.mpr
      refine ⟨s(p.getVert k,p.getVert (k+1)),?_,?_⟩
      · apply List.mem_toFinset.mpr
        exact (p.mk_mem_edges_iff_exists).mpr ⟨k,by omega,rfl⟩
      · change s(f (p.getVert k),f (p.getVert (k+1)))=s(x,y)
        rw [hmap k (by omega),hmap (k+1) (by omega)]
        exact hxy
end Oberwolfach
