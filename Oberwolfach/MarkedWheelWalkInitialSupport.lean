module

public import Oberwolfach.MarkedSingleWheelWalk

@[expose] public section
/-! The initial support of a marked wheel's physical walk is exactly its
 auxiliary rim vertices; its final vertex is the successor endpoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_sequence_dropLast_of_prefix {V:Type*} (m:ℕ)
    (f:Fin ((m+1)+1)→V) (g:Fin (m+1)→V)
    (h:∀i:Fin (m+1),f i.castSucc=g i):
    (List.ofFn f).dropLast=List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    have hi':i<m+1:=by simpa using hj
    simp only [List.getElem_dropLast,List.getElem_ofFn]
    exact h ⟨i,hi'⟩

theorem marked_wheel_walk_initial_support
    {V E K:Type*} (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b)
    (C:MarkedCycleTuple tail head ktail khead m π b)
    (hroot:π (C.val 0)≠C.val 0)
    (hE:∀e:E,G.Adj (tail e) (head e))
    (hK:∀e:K,G.Adj (ktail e) (π (khead e))):
    ∃p:G.Walk (C.val 0) (π (C.val 0)),
      p.IsPath ∧ p.length=m+1 ∧ p.support.dropLast=List.ofFn C.val := by
  obtain ⟨f,hprefix,_,p,hp,hlen,hsupp⟩:=marked_single_wheel_physical_walk G tail head ktail khead m b π hb C hroot hE hK
  refine ⟨p,hp,hlen,?_⟩
  rw [hsupp]
  exact finite_sequence_dropLast_of_prefix m f C.val hprefix
end Oberwolfach
