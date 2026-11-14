module

public import Oberwolfach.ActualBufferedFinalPathIdentification

@[expose] public section
/-! Recover the whole buffered source walk from the exact support sequence. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem buffered_source_walk_from_support
    {X:Type} [Fintype X] [DecidableEq X] (F:SimpleGraph X) (L:ℕ)
    (ext:Fin (L+5)↪X) {u v:X} (p:F.Walk u v)
    (hsupp:p.support=List.ofFn ext):
    ∃q:F.Walk (ext 0) (ext (Fin.last (L+4))),q.length=L+4 ∧ q.support=List.ofFn ext:=by
  have hlen:p.length=L+4:=by
    have hh:=congrArg List.length hsupp
    simp only [SimpleGraph.Walk.length_support,List.length_ofFn] at hh
    omega
  have hv:∀j:ℕ,(hj:j≤L+4)→p.getVert j=ext ⟨j,by omega⟩:=by
    intro j hj
    have hh:some (p.getVert j)=p.support[j]? :=p.getVert_eq_support_getElem? (by omega)
    rw [hsupp] at hh
    simpa only [List.getElem?_ofFn,dif_pos (show j<L+5 by omega),Option.some.injEq] using hh
  have hu:u=ext 0:=by
    have hh:=hv 0 (by omega)
    rw [SimpleGraph.Walk.getVert_zero] at hh
    have hi:(⟨0,by omega⟩:Fin (L+5))=0:=by apply Fin.ext; rfl
    exact hh.trans (congrArg ext hi)
  have hend:v=ext (Fin.last (L+4)):=by
    have hh:=hv (L+4) (by omega)
    have he:p.getVert (L+4)=v:=by simpa only [hlen] using p.getVert_length
    have hi:(⟨L+4,by omega⟩:Fin (L+5))=Fin.last (L+4):=by apply Fin.ext; rfl
    exact he.symm.trans (hh.trans (congrArg ext hi))
  let q:=p.copy hu hend
  refine ⟨q,?_,?_⟩
  · simpa only [q,SimpleGraph.Walk.length_copy] using hlen
  · simpa only [q,SimpleGraph.Walk.support_copy] using hsupp
end Oberwolfach
