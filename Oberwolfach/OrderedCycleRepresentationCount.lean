module

public import Oberwolfach.OrderedCycleRepresentationEdges
public import Oberwolfach.OrdinaryWheelResources

@[expose] public section
/-! Every cycle of length r has exactly 2r ordered representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def directedEdgesEquivDart {V:Type} (H:SimpleGraph V):DirectedEdges H≃H.Dart where
  toFun e:=⟨e.val,e.property⟩
  invFun e:=⟨e.toProd,e.adj⟩
  left_inv e:=by cases e;rfl
  right_inv e:=by cases e;rfl

theorem ordered_cycle_representation_card {V:Type} [Fintype V] [DecidableEq V]
    (H:SimpleGraph V) (n:ℕ) (hn:1≤n) (hH:IsEmbeddedCycle H (n+2)):
    Fintype.card (OrderedCycleRepresentations H (n+2))=2*(n+2):=by
  calc
    _ = Fintype.card (DirectedEdges H) := Fintype.card_congr (orderedCycleFirstEdgeEquiv H n hn hH)
    _ = Fintype.card H.Dart := Fintype.card_congr (directedEdgesEquivDart H)
    _ = 2*H.edgeFinset.card := H.dart_card_eq_twice_card_edges
    _ = _ := by rw [hH.edgeFinset_card]
end Oberwolfach
