module

public import Oberwolfach.FiniteSequenceWalkEdges

@[expose] public section
/-! The oriented darts of a walk follow its finite vertex sequence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sequence_walk_dart_at
    {V:Type*} [DecidableEq V] (G:SimpleGraph V) (n:ℕ) (f:Fin (n+1)→V)
    {a b:V} (p:G.Walk a b) (hlen:p.length=n) (hsupp:p.support=List.ofFn f)
    (i:Fin n):
    (p.darts[i.val]' (by simpa [SimpleGraph.Walk.length_darts,hlen] using i.isLt)).toProd=
      (f i.castSucc,f i.succ) := by
  have hv:∀j:ℕ,(hj:j≤n)→p.getVert j=f ⟨j,by omega⟩:=by
    intro j hj
    have hh:=p.getVert_eq_support_getElem? (n:=j) (by omega)
    rw [hsupp] at hh
    simpa only [List.getElem?_ofFn, dif_pos (show j<n+1 by omega), Option.some.injEq] using hh
  have hedge:i.val<p.darts.length:=by simpa [SimpleGraph.Walk.length_darts,hlen] using i.isLt
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert i.val hedge]
  simp only [hv i.val (by omega),hv (i.val+1) (by omega)]
  have h1:(⟨i.val,by omega⟩:Fin (n+1))=i.castSucc:=by apply Fin.ext;rfl
  have h2:(⟨i.val+1,by omega⟩:Fin (n+1))=i.succ:=by apply Fin.ext;rfl
  rw [h1,h2]
end Oberwolfach
