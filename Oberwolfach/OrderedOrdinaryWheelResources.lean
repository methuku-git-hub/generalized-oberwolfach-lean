module

public import Oberwolfach.RawMarkedCandidateGeometry
public import Oberwolfach.CycleEdgeEnumeration

@[expose] public section
/-! Ordered separated ordinary cycles with their hub and physical requests. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def OrderedOrdinaryWheel (π:Equiv.Perm V) (b r:ℕ):Type :=
  {C:Fin r→V // PermutationSeparated π b C}×U

instance (π:Equiv.Perm V) (b r:ℕ):Fintype (OrderedOrdinaryWheel (U:=U) π b r) := by
  unfold OrderedOrdinaryWheel
  infer_instance

def orderedOrdinaryResources {π:Equiv.Perm V} {b r:ℕ} (W:OrderedOrdinaryWheel (U:=U) π b r):
    Finset ((V×V)⊕(V×U)) :=
  Finset.univ.image (fun i:Fin r=>Sum.inl (W.1.val i,W.1.val (cycleNext i))) ∪
    Finset.univ.image (fun i:Fin r=>Sum.inr (W.1.val i,W.2))

theorem orderedOrdinaryResources_rim {π:Equiv.Perm V} {b r:ℕ} (W:OrderedOrdinaryWheel (U:=U) π b r) (e:V×V):
    Sum.inl e∈orderedOrdinaryResources W ↔ ∃ i:Fin r,(W.1.val i,W.1.val (cycleNext i))=e :=by
  simp [orderedOrdinaryResources]

theorem orderedOrdinaryResources_spoke {π:Equiv.Perm V} {b r:ℕ} (W:OrderedOrdinaryWheel (U:=U) π b r) (e:V×U):
    Sum.inr e∈orderedOrdinaryResources W ↔ ∃ i:Fin r,(W.1.val i,W.2)=e :=by
  simp [orderedOrdinaryResources]

theorem orderedOrdinaryPhysical_edge_injective {π:Equiv.Perm V} {b r:ℕ} (hr:3≤r)
    (W:OrderedOrdinaryWheel (U:=U) π b r):
    Function.Injective (fun i:Fin r=>s(W.1.val i,W.1.val (cycleNext i))) := by
  let f:Fin r ↪ V:=⟨W.1.val,permutationSeparated_injective π b W.1.val W.1.property⟩
  exact cycle_edge_injective hr f
end Oberwolfach
