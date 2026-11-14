module

public import Oberwolfach.FiniteSequenceWalkEdgeSet
public import Oberwolfach.MarkedSingleWheelWalkEdges
public import Oberwolfach.MarkedWheelWalkInitialSupport
public import Oberwolfach.MarkedPhysicalCycleProperties

@[expose] public section
/-! A single marked wheel's physical path has exactly its typed rim's
 physical edge set and its auxiliary rim as initial support. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_wheel_walk_physical_edge_set
    {V E K:Type*} [DecidableEq V] (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃p:G.Walk (C.val 0) (π (C.val 0)),
      p.IsPath ∧ p.length=m+1 ∧ p.support.dropLast=List.ofFn C.val ∧
      walkPhysicalEdges p=markedCyclePhysicalEdges tail head ktail khead m π b C := by
  obtain ⟨f,hprefix,hlast,p,hlen,hp,hsupp,_⟩:=marked_single_wheel_walk_edges G tail head ktail khead m b π hb C hroot hE hK
  refine ⟨p,hp,hlen,?_,?_⟩
  · rw [hsupp]
    exact finite_sequence_dropLast_of_prefix m f C.val hprefix
  · rw [finite_sequence_walk_edge_set G (m+1) f p hlen hsupp]
    unfold markedCyclePhysicalEdges
    apply Finset.image_congr
    intro i hi
    exact (marked_wheel_physical_edge_order tail head ktail khead m b π C f hprefix hlast i).symm
end Oberwolfach
