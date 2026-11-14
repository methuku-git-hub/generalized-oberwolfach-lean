module

public import Oberwolfach.OrdinaryPhysicalEditOfEqualRims
public import Oberwolfach.HubToRowDeletion

@[expose] public section
/-! Typed rim and spoke changes combine on the same physical graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_physical_edit_of_equal_spokes
    (R Q:SimpleGraph V) (H:V→U→Prop) (L:ℝ) (hL:0≤L)
    (hr:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L):
    ∀a:V⊕U,((changed ((ordinaryPhysicalGraph R H).neighborFinset a)
      ((ordinaryPhysicalGraph Q H).neighborFinset a)).card:ℝ)≤L:=by
  intro a
  cases a with
  | inl v=>
    have he:changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inl v))
        ((ordinaryPhysicalGraph Q H).neighborFinset (Sum.inl v))=
        (changed (R.neighborFinset v) (Q.neighborFinset v)).image Sum.inl:=by
      ext b
      cases b <;> simp [changed,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [he,Finset.card_image_of_injective _ Sum.inl_injective]
    exact hr v
  | inr u=>
    have he:changed ((ordinaryPhysicalGraph R H).neighborFinset (Sum.inr u))
        ((ordinaryPhysicalGraph Q H).neighborFinset (Sum.inr u))=∅:=by
      ext b
      cases b <;> simp [changed,ordinaryPhysicalGraph,SimpleGraph.mem_neighborFinset]
    rw [he]
    simpa using hL

theorem ordinary_physical_edit_from_typed_changes
    (R Q:SimpleGraph V) (J H:V→U→Prop) (Lrim Lspoke:ℝ) (hR:0≤Lrim)
    (hr:∀v,((changed (R.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤Lrim)
    (hrow:∀v,((changed (Finset.univ.filter (J v)) (Finset.univ.filter (H v))).card:ℝ)≤Lspoke)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>J v u)) (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤Lspoke):
    ∀a:V⊕U,((changed ((ordinaryPhysicalGraph R J).neighborFinset a)
      ((ordinaryPhysicalGraph Q H).neighborFinset a)).card:ℝ)≤Lrim+Lspoke:=by
  intro a
  have h1:=ordinary_physical_edit_of_equal_spokes R Q J Lrim hR hr a
  have h2:=ordinary_physical_edit_of_equal_rims Q J H Lspoke hrow hcol a
  have ht:((changed ((ordinaryPhysicalGraph R J).neighborFinset a)
      ((ordinaryPhysicalGraph Q H).neighborFinset a)).card:ℝ)≤
      ((changed ((ordinaryPhysicalGraph R J).neighborFinset a) ((ordinaryPhysicalGraph Q J).neighborFinset a)).card:ℝ)+
      ((changed ((ordinaryPhysicalGraph Q J).neighborFinset a) ((ordinaryPhysicalGraph Q H).neighborFinset a)).card:ℝ):=by
    exact_mod_cast changed_card_triangle ((ordinaryPhysicalGraph R J).neighborFinset a)
      ((ordinaryPhysicalGraph Q J).neighborFinset a) ((ordinaryPhysicalGraph Q H).neighborFinset a)
  linarith only [ht,h1,h2]
end Oberwolfach
