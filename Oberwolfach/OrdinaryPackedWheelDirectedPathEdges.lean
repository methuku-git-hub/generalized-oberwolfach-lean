module

public import Oberwolfach.OrdinaryPackedWheelDirectedPath

@[expose] public section
/-! Retain the original ordered ordinary rim arc responsible for every edge
of the constructed cycle-tail path. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_packed_wheel_directed_path_with_edges
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (b n:ℕ) (hn:2≤n) (W:OrderedOrdinaryWheel (U:=U) π b (n+1))
    (R:V→V→Prop) (hR:∀i:Fin (n+1),R (W.1.val i) (W.1.val (cycleNext i))):
    let start:=W.1.val (cycleNext 0)
    let finish:=W.1.val 0
    ∃q:(SimpleGraph.completeGraph V).Walk start finish,
      q.IsPath ∧ q.length=n ∧
      q.support.toFinset=Finset.univ.image W.1.val ∧
      R finish start ∧
      (∀k,k<q.length→∃i:Fin (n+1),q.getVert k=W.1.val i ∧ q.getVert (k+1)=W.1.val (cycleNext i)) ∧
      (∀k,k<q.length→R (q.getVert k) (q.getVert (k+1))):=by
  intro start finish
  let S:V→V→Prop:=fun x y=>R x y ∧ ∃i:Fin (n+1),x=W.1.val i ∧ y=W.1.val (cycleNext i)
  obtain ⟨q,hp,hl,hs,hclose,hedges⟩:=ordinary_packed_wheel_directed_path π b n hn W S
    (fun i=>⟨hR i,i,rfl,rfl⟩)
  exact ⟨q,hp,hl,hs,hclose.1,fun k hk=>(hedges k hk).2,fun k hk=>(hedges k hk).1⟩
end Oberwolfach
