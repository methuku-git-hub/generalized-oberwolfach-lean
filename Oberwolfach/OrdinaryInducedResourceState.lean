module

public import Oberwolfach.OrdinaryInducedRawResource

@[expose] public section
/-! The inner resource state is exactly the state of its physical ambient
resource, for arbitrary rim graphs and spoke relations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_resource_state_eq (Q : SimpleGraph V) (H : V → U → Prop)
    (A : Set V) (u : U) (a : Sym2 A ⊕ (A × Unit)) :
    ordinaryResourceState (Q.induce A) (fun x (_ : Unit) => H x.val u) a =
      ordinaryResourceState Q H (ordinaryInducedRawResource A u a) := by
  cases a with
  | inl a =>
    induction a using Sym2.ind with
    | _ x y =>
      have hm : Sym2.map Subtype.val s(x,y) = s(x.val,y.val) := rfl
      change ordinaryResourceState (Q.induce A) (fun x (_ : Unit) => H x.val u) (Sum.inl s(x,y)) =
        ordinaryResourceState Q H (Sum.inl (Sym2.map Subtype.val s(x,y)))
      rw [hm]
      simp only [ordinaryResourceState, Sum.elim_inl, SimpleGraph.mem_edgeSet, SimpleGraph.induce_adj]
  | inr a =>
    simp only [ordinaryInducedRawResource, ordinaryResourceState, Sum.elim_inr]
end Oberwolfach
