module

public import Oberwolfach.RegularTwoBufferedPathLocalEmbedding
public import Oberwolfach.FiniteSequenceRangeEmbedding

@[expose] public section
/-! Match a buffered source path in a 2-regular graph to an injective target
path with the same indexed length. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem regular_two_buffered_path_target_embedding
    {V W:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hG:G.IsRegularOfDegree 2) (H:SimpleGraph W) (n:ℕ)
    (ext:Fin (n+5)↪V) (inner:Fin (n+1)↪V)
    (hinner:∀k,inner k=ext ⟨k.val+2,by omega⟩)
    (hstep:∀k:Fin (n+4),G.Adj (ext ⟨k.val,by omega⟩) (ext ⟨k.val+1,by omega⟩))
    (target:Fin (n+1)↪W)
    (htarget:∀k:Fin n,H.Adj (target ⟨k.val,by omega⟩) (target ⟨k.val+1,by omega⟩)):
    ∃f:{x // x∈Finset.univ.image inner}↪W,
      (∀k:Fin (n+1),f ⟨inner k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩=target k) ∧
      Set.range f⊆Set.range target ∧
      (∀x y,G.Adj x.val y.val→H.Adj (f x) (f y)):=by
  classical
  obtain ⟨f,hf⟩:=finite_sequence_range_embedding (n+1) inner target
  refine ⟨f,hf,?_,?_⟩
  · rintro z ⟨x,rfl⟩
    obtain ⟨p,_,hp⟩:=Finset.mem_image.mp x.property
    refine ⟨p,?_⟩
    simpa only [hp] using (hf p).symm
  · intro x y hxy
    obtain ⟨p,_,hp⟩:=Finset.mem_image.mp x.property
    obtain ⟨q,_,hq⟩:=Finset.mem_image.mp y.property
    have hfx:f x=target p:=by simpa only [hp] using hf p
    have hfy:f y=target q:=by simpa only [hq] using hf q
    have hsource:G.Adj (inner p) (inner q):=by simpa only [hp,hq] using hxy
    have hindex:=regular_two_buffered_path_adjacent_indices G hG n ext inner hinner hstep p q hsource
    rw [hfx,hfy]
    rcases hindex with hpq|hqp
    · have hpbound:p.val<n:=by omega
      have ha:=htarget ⟨p.val,hpbound⟩
      have hp':(⟨p.val,by omega⟩:Fin (n+1))=p:=Fin.ext rfl
      have hq':(⟨p.val+1,by omega⟩:Fin (n+1))=q:=Fin.ext hpq
      simpa only [hp',hq'] using ha
    · have hqbound:q.val<n:=by omega
      have ha:=(htarget ⟨q.val,hqbound⟩).symm
      have hq':(⟨q.val,by omega⟩:Fin (n+1))=q:=Fin.ext rfl
      have hp':(⟨q.val+1,by omega⟩:Fin (n+1))=p:=Fin.ext hqp
      simpa only [hp',hq'] using ha
end Oberwolfach
