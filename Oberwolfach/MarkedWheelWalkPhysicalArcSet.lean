module

public import Oberwolfach.FiniteSequenceWalkArcSet
public import Oberwolfach.MarkedSingleWheelWalkArcs
public import Oberwolfach.MarkedWheelWalkPhysicalEdgeSet

@[expose] public section
/-! A marked wheel's simple physical path has exactly its ordered physical
rim arcs as well as its physical rim edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def markedCyclePhysicalArcs {V E K:Type*} [DecidableEq V]
    (tail head:E→V) (ktail khead:K→V) (m:ℕ) (π:Equiv.Perm V) (b:ℕ)
    (C:MarkedCycleTuple tail head ktail khead m π b):Finset (V×V) :=
  Finset.univ.image (markedPhysicalArc tail head ktail khead π ∘
    markedCycleTypedEdge tail head ktail khead m π b C)

theorem marked_wheel_walk_physical_arc_set
    {V E K:Type*} [DecidableEq V] (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃p:G.Walk (C.val 0) (π (C.val 0)),
      p.IsPath ∧ p.length=m+1 ∧ p.support.dropLast=List.ofFn C.val ∧
      walkPhysicalEdges p=markedCyclePhysicalEdges tail head ktail khead m π b C ∧
      walkPhysicalArcs p=markedCyclePhysicalArcs tail head ktail khead m π b C := by
  obtain ⟨f,hprefix,hlast,p,hlen,hp,hsupp,_⟩:=marked_single_wheel_walk_arcs G tail head ktail khead m b π hb C hroot hE hK
  refine ⟨p,hp,hlen,?_,?_,?_⟩
  · rw [hsupp]
    exact finite_sequence_dropLast_of_prefix m f C.val hprefix
  · rw [finite_sequence_walk_edge_set G (m+1) f p hlen hsupp]
    unfold markedCyclePhysicalEdges
    apply Finset.image_congr
    intro i hi
    exact (marked_wheel_physical_edge_order tail head ktail khead m b π C f hprefix hlast i).symm
  · rw [finite_sequence_walk_arc_set G (m+1) f p hlen hsupp]
    unfold markedCyclePhysicalArcs
    apply Finset.image_congr
    intro i hi
    exact (marked_wheel_physical_arc_order tail head ktail khead m b π C f hprefix hlast i).symm
end Oberwolfach
