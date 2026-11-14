module

public import Oberwolfach.OrdinaryComponentToWheel
public import Oberwolfach.OrderedOrdinaryWheelResources
public import Oberwolfach.CycleCopies

@[expose] public section
/-! The separated cyclic tuple of an ordinary matching candidate determines
an actual universal wheel and the matching rim vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def orderedOrdinaryUniversalWheel {r b:ℕ} {π:Equiv.Perm V}
    (hr:3≤r) (W:OrderedOrdinaryWheel (U:=U) π b r):UniversalOrdinaryWheel V U r :=
  let f:Fin r↪V:=⟨W.1.val,permutationSeparated_injective π b W.1.val W.1.property⟩
  ⟨(⟨⟨(SimpleGraph.cycleGraph r).map f,⟨hr,f,rfl⟩⟩,le_top⟩,W.2),
    ⟨fun _ _=>trivial,fun _ _ _ _=>not_false⟩⟩

theorem ordered_ordinary_universal_hub {r b:ℕ} {π:Equiv.Perm V}
    (hr:3≤r) (W:OrderedOrdinaryWheel (U:=U) π b r):
    ordinaryWheelHub (orderedOrdinaryUniversalWheel hr W)=W.2:=rfl

theorem ordered_ordinary_universal_support {r b:ℕ} {π:Equiv.Perm V}
    (hr:3≤r) (W:OrderedOrdinaryWheel (U:=U) π b r):
    (ordinaryWheelRim (orderedOrdinaryUniversalWheel hr W)).support=Set.range W.1.val :=by
  dsimp only [orderedOrdinaryUniversalWheel,ordinaryWheelRim]
  rw [cycle_map_support hr]
  rfl

theorem ordered_ordinary_component_embedding {n r b:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:SimpleGraph (Fin n)) (hF:F.IsRegularOfDegree 2) (C:F.ConnectedComponent)
    (hr:3≤r) (hC:Fintype.card C=r) (π:Equiv.Perm (Fin n))
    (W:OrderedOrdinaryWheel (U:=U) π b r):
    ∃f:C↪Fin n, Set.range f=Set.range W.1.val ∧
      ∀x y:C,C.toSimpleGraph.Adj x y↔(ordinaryWheelRim (orderedOrdinaryUniversalWheel hr W)).Adj (f x) (f y) :=by
  obtain ⟨f,hf,hg⟩:=ordinary_component_to_wheel F hF C hC (orderedOrdinaryUniversalWheel hr W)
  refine ⟨f,?_,hg⟩
  rw [←ordered_ordinary_universal_support hr W]
  exact hf
end Oberwolfach
