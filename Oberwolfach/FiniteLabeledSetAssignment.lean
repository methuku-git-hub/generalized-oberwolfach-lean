module

public import Oberwolfach.FiberwiseFiniteAssignment
public import Mathlib.Data.Finset.Card

@[expose] public section
/-! Label-by-label cardinality bounds produce one injection of the whole
selected set, preserving every label. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_labeled_set_assignment {A B I:Type} [DecidableEq A] [DecidableEq B]
    (S:Finset A) (T:Finset B) (la:A→I) (lb:B→I)
    (h:∀i:I,(S.filter (fun a=>la a=i)).card≤(T.filter (fun b=>lb b=i)).card):
    ∃f:↥S↪↥T,∀a,lb (f a).val=la a.val :=by
  classical
  apply fiberwise_finite_assignment (fun a:↥S=>la a.val) (fun b:↥T=>lb b.val)
  intro i
  let ea:{a:↥S // la a.val=i} ≃ ↥(S.filter (fun a=>la a=i)) := {
    toFun:=fun a=>⟨a.val.val,Finset.mem_filter.mpr ⟨a.val.property,a.property⟩⟩
    invFun:=fun a=>⟨⟨a.val,(Finset.mem_filter.mp a.property).1⟩,(Finset.mem_filter.mp a.property).2⟩
    left_inv:=by intro a;cases a;rfl
    right_inv:=by intro a;cases a;rfl }
  let eb:{b:↥T // lb b.val=i} ≃ ↥(T.filter (fun b=>lb b=i)) := {
    toFun:=fun b=>⟨b.val.val,Finset.mem_filter.mpr ⟨b.val.property,b.property⟩⟩
    invFun:=fun b=>⟨⟨b.val,(Finset.mem_filter.mp b.property).1⟩,(Finset.mem_filter.mp b.property).2⟩
    left_inv:=by intro b;cases b;rfl
    right_inv:=by intro b;cases b;rfl }
  rw [Fintype.card_congr ea,Fintype.card_congr eb]
  simpa only [Fintype.card_coe] using h i
end Oberwolfach
