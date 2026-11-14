module

public import Oberwolfach.MarkedSpokePairIdentity

@[expose] public section

/-! The vertex-wheel pair has a common hub, so its free spokes cancel.
Only the two fixed attachment edges and the old-root spoke remain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}
 theorem marked_vertex_pair_integer_identity (n:ℕ) (hn:2≤n)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (p:Fin (n+1)→V) (v v':V) (u:U) (j:Bool)
    (C D:MarkedWheel tail head ktail khead (n+1) π b H₀ HK)
    (hC:∀ i,C.1.val i=rootedCycleOrder (markedRootOrder (n+1) j) v p i)
    (hD:∀ i,D.1.val i=rootedCycleOrder (markedRootOrder (n+1) j) v' p i)
    (hCu:C.2.val=u) (hDu:D.2.val=u) (e:Finset V⊕(V×U)):
    (if e∈markedWheelPhysicalResources C then (1:ℤ) else 0)-
      (if e∈markedWheelPhysicalResources D then 1 else 0)=
      physicalIntDelta (Sum.inl {v,p 0}) (Sum.inl {v',p 0}) e+
      physicalIntDelta (Sum.inl (if j then {p (Fin.last n),π v} else {p (Fin.last n),v}))
        (Sum.inl (if j then {p (Fin.last n),π v'} else {p (Fin.last n),v'})) e+
      physicalIntDelta (Sum.inr (v,u)) (Sum.inr (v',u)) e:=by
  have hh:=marked_spoke_pair_integer_identity n hn hp p v v' u u j C D hC hD hCu hDu e
  have hz:∀ i:Fin (n+1),physicalIntDelta (Sum.inr (p i,u):Finset V⊕(V×U)) (Sum.inr (p i,u)) e=0:=by
    intro i;exact sub_self _
  simpa only [hz,Finset.sum_const_zero,add_zero] using hh
end Oberwolfach
