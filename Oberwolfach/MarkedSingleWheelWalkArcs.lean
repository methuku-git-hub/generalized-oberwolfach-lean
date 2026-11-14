module

public import Oberwolfach.FiniteSequenceWalkDarts
public import Oberwolfach.MarkedWheelPhysicalArcOrder

@[expose] public section
/-! The simple physical walk of a marked wheel traverses exactly the
wheel's physical rim edge at each position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_single_wheel_walk_arcs
    {V E K:Type*} [DecidableEq V] (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃f:Fin ((m+1)+1)↪V,
      (∀i:Fin (m+1),f i.castSucc=C.val i) ∧ f (Fin.last (m+1))=π (C.val 0) ∧
    ∃p:G.Walk (C.val 0) (π (C.val 0)), ∃hlen:p.length=m+1,
      p.IsPath ∧ p.support=List.ofFn f ∧
      ∀i:Fin (m+1),
        (p.darts[i.val]' (by simpa [SimpleGraph.Walk.length_darts,hlen] using i.isLt)).toProd=
          markedPhysicalArc tail head ktail khead π (markedCycleTypedEdge tail head ktail khead m π b C i) := by
  obtain ⟨f,hprefix,hlast,p,hp,hlen,hsupp⟩:=marked_single_wheel_physical_walk G tail head ktail khead m b π hb C hroot hE hK
  refine ⟨f,hprefix,hlast,p,hlen,hp,hsupp,?_⟩
  intro i
  exact (finite_sequence_walk_dart_at G (m+1) f p hlen hsupp i).trans
    (marked_wheel_physical_arc_order tail head ktail khead m b π C f hprefix hlast i).symm
end Oberwolfach
