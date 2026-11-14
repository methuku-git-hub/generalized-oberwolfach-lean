module

public import Oberwolfach.MarkedSingleWheelWalk
public import Oberwolfach.MarkedPhysicalEdges

@[expose] public section
/-! The consecutive edges in the physical rim sequence are the actual
 physical images of the wheel's typed rim arcs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedPhysicalArc {V E K:Type*} (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V):E⊕K→V×V :=
  Sum.elim (fun e=>(tail e,head e)) (fun e=>(ktail e,π (khead e)))

theorem marked_wheel_physical_arc_order
    {V E K:Type*} [DecidableEq V] (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (C:MarkedCycleTuple tail head ktail khead m π b)
    (f:Fin ((m+1)+1)→V) (hprefix:∀i:Fin (m+1),f i.castSucc=C.val i)
    (hlast:f (Fin.last (m+1))=π (C.val 0)) (i:Fin (m+1)):
    markedPhysicalArc tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C i)=
      (f i.castSucc,f i.succ) := by
  refine Fin.lastCases ?_ (fun j=>?_) i
  · have he:=Classical.choose_spec C.property.2.2
    simp only [markedCycleTypedEdge,Fin.snoc_last,markedPhysicalArc,Sum.elim_inr]
    rw [he.1,he.2]
    have hpos:(Fin.last m).succ=Fin.last (m+1):=by apply Fin.ext; rfl
    rw [hprefix (Fin.last m),hpos,hlast]
  · have he:=Classical.choose_spec (C.property.2.1 j)
    simp only [markedCycleTypedEdge,Fin.snoc_castSucc,markedPhysicalArc,Sum.elim_inl]
    rw [he.1,he.2]
    have hpos:j.castSucc.succ=j.succ.castSucc:=by apply Fin.ext; rfl
    rw [hprefix j.castSucc,hpos,hprefix j.succ]
end Oberwolfach
