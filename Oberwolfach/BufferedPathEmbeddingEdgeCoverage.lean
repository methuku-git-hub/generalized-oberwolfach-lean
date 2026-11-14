module

public import Oberwolfach.BufferedWalkEmbeddingGlue
public import Oberwolfach.RegularTwoBufferedPathLocalEmbedding

@[expose] public section
/-! Every mapped source edge follows a consecutive pair on one matching
target path, so disjoint target path edges can be used factor by factor. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_embedding_edge_coverage
    {V W I:Type*} [Fintype V] [DecidableEq V] [DecidableEq I]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2)
    (n:I→ℕ) (ext:∀i,Fin (n i+5)↪V) (inner:∀i,Fin (n i+1)↪V)
    (hinner:∀i k,inner i k=ext i ⟨k.val+2,by omega⟩)
    (hwalk:∀i,∃p:G.Walk (ext i ⟨0,by omega⟩) (ext i ⟨n i+4,by omega⟩),
      p.length=n i+4 ∧ p.support=List.ofFn (ext i))
    (hdis:∀i j,i≠j→Disjoint (Finset.univ.image (ext i)) (Finset.univ.image (ext j)))
    (A:Finset I) (target:∀i,Fin (n i+1)→W)
    (φ:{x // x∈A.biUnion (fun i=>Finset.univ.image (inner i))}→W)
    (hmatch:∀i (hi:i∈A) (k:Fin (n i+1)),
      φ ⟨inner i k,Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩=target i k):
    ∀x y,G.Adj x.val y.val→∃i∈A,∃k:Fin (n i),
      (φ x=target i k.castSucc ∧ φ y=target i k.succ) ∨
      (φ y=target i k.castSucc ∧ φ x=target i k.succ):=by
  classical
  intro x y hxy
  obtain ⟨i,hi,hxi,hyi⟩:=regular_two_buffered_walk_edge_cover G hG n ext inner hinner hwalk hdis A
    x.val y.val x.property y.property hxy
  obtain ⟨p,_,hp⟩:=Finset.mem_image.mp hxi
  obtain ⟨q,_,hq⟩:=Finset.mem_image.mp hyi
  have hfx:φ x=target i p:=by simpa only [hp] using hmatch i hi p
  have hfy:φ y=target i q:=by simpa only [hq] using hmatch i hi q
  have hsource:G.Adj (inner i p) (inner i q):=by simpa only [hp,hq] using hxy
  obtain ⟨walk,hlen,hsupport⟩:=hwalk i
  have hstep:∀k:Fin (n i+4),G.Adj (ext i ⟨k.val,by omega⟩) (ext i ⟨k.val+1,by omega⟩):=by
    intro k
    exact walk_ofFn_support_adjacent G (n i+4) (ext i) walk hlen hsupport k
  have hindex:=regular_two_buffered_path_adjacent_indices G hG (n i) (ext i) (inner i) (hinner i) hstep p q hsource
  rcases hindex with hpq|hqp
  · have hpbound:p.val<n i:=by omega
    let k:Fin (n i):=⟨p.val,hpbound⟩
    have hp':k.castSucc=p:=Fin.ext rfl
    have hq':k.succ=q:=Fin.ext hpq
    refine ⟨i,hi,k,Or.inl ?_⟩
    simpa only [hp',hq'] using And.intro hfx hfy
  · have hqbound:q.val<n i:=by omega
    let k:Fin (n i):=⟨q.val,hqbound⟩
    have hq':k.castSucc=q:=Fin.ext rfl
    have hp':k.succ=p:=Fin.ext hqp
    refine ⟨i,hi,k,Or.inr ?_⟩
    simpa only [hq',hp'] using And.intro hfy hfx
end Oberwolfach
