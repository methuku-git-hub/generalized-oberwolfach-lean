module

public import Oberwolfach.EmbeddedClassChanges
public import Oberwolfach.MarkedBoundaryNeighbourhoods

@[expose] public section

/-! Exact transport of the actual hub classes to a fixed inner vertex
set. The original spoke predicates and physical coins are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W V U:Type} [Fintype W] [DecidableEq W] [DecidableEq V]

theorem embedded_filtered_class_image (f:W↪V) (P:V→Prop):
    (Finset.univ.filter (fun w=>P (f w))).image f=(Finset.univ.image f).filter P:=
  (filter_image_class f Finset.univ P).symm

theorem embedded_filtered_class_card (f:W↪V) (P Q:V→Prop):
    ((Finset.univ.filter (fun w=>P (f w))).filter (fun w=>Q (f w))).card=
      (((Finset.univ.image f).filter P).filter Q).card:=by
  rw [filter_image_class,filter_image_class,Finset.card_image_of_injective _ f.injective]

theorem embedded_filtered_class_change_card (f:W↪V) (P Q:V→Prop):
    (changed (Finset.univ.filter (fun w=>P (f w))) (Finset.univ.filter (fun w=>Q (f w)))).card=
      (changed ((Finset.univ.image f).filter P) ((Finset.univ.image f).filter Q)).card:=by
  rw [←embedded_filtered_class_image,←embedded_filtered_class_image,changed_image_card f f.injective]

theorem embedded_boundary_hub_class_image [Fintype V] [Fintype U] [DecidableEq U]
    (f:W↪V) (H₀ HK:V→U→Prop) (u:U) (τ:Sym2 (V⊕U)→Bool):
    (Finset.univ.filter (fun w=>(H₀ (f w) u∨HK (f w) u)∧τ s(Sum.inl (f w),Sum.inr u)=true)).image f=
      markedBoundarySpokeRows H₀ HK (Finset.univ.image f) τ u:=by
  unfold markedBoundarySpokeRows
  convert embedded_filtered_class_image f (fun x=>(H₀ x u∨HK x u)∧τ s(Sum.inl x,Sum.inr u)=true) using 1 <;> congr!
end Oberwolfach
