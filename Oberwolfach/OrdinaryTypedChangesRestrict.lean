module

public import Oberwolfach.OrdinaryInnerPhysicalComap

@[expose] public section
/-! Rim, spoke-row and spoke-column edit bounds do not increase when the
same two hosts are restricted along fixed injective vertex and hub maps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W U Z:Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

theorem ordinary_relation_change_restrict_le
    (H J:V→U→Prop) (f:W↪V) (g:Z↪U):
    (∀v:W,(changed (Finset.univ.filter (fun u:Z=>H (f v) (g u)))
      (Finset.univ.filter (fun u:Z=>J (f v) (g u)))).card≤
      (changed (Finset.univ.filter (H (f v))) (Finset.univ.filter (J (f v)))).card) ∧
    (∀u:Z,(changed (Finset.univ.filter (fun v:W=>H (f v) (g u)))
      (Finset.univ.filter (fun v:W=>J (f v) (g u)))).card≤
      (changed (Finset.univ.filter (fun v:V=>H v (g u))) (Finset.univ.filter (fun v:V=>J v (g u)))).card) :=by
  constructor
  · intro v
    have hsub:(changed (Finset.univ.filter (fun u:Z=>H (f v) (g u)))
        (Finset.univ.filter (fun u:Z=>J (f v) (g u)))).image g⊆
        changed (Finset.univ.filter (H (f v))) (Finset.univ.filter (J (f v))):=by
      intro x hx
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hx
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] using hu
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ g.injective] at hh
    exact hh
  · intro u
    have hsub:(changed (Finset.univ.filter (fun v:W=>H (f v) (g u)))
        (Finset.univ.filter (fun v:W=>J (f v) (g u)))).image f⊆
        changed (Finset.univ.filter (fun v:V=>H v (g u))) (Finset.univ.filter (fun v:V=>J v (g u))):=by
      intro x hx
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hx
      simpa only [changed,Finset.mem_union,Finset.mem_sdiff,Finset.mem_filter,Finset.mem_univ,true_and] using hv
    have hh:=Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ f.injective] at hh
    exact hh

theorem ordinary_typed_changes_restrict
    (P Q:SimpleGraph V) (H J:V→U→Prop) (f:W↪V) (g:Z↪U) (L:ℝ)
    (hr:∀v,((changed (P.neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hrow:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (J v))).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>H v u)) (Finset.univ.filter (fun v=>J v u))).card:ℝ)≤L):
    (∀v:W,((changed ((P.comap f).neighborFinset v) ((Q.comap f).neighborFinset v)).card:ℝ)≤L) ∧
    (∀v:W,((changed (Finset.univ.filter (fun u:Z=>H (f v) (g u)))
      (Finset.univ.filter (fun u:Z=>J (f v) (g u)))).card:ℝ)≤L) ∧
    (∀u:Z,((changed (Finset.univ.filter (fun v:W=>H (f v) (g u)))
      (Finset.univ.filter (fun v:W=>J (f v) (g u)))).card:ℝ)≤L) :=by
  obtain ⟨hrow',hcol'⟩:=ordinary_relation_change_restrict_le H J f g
  refine ⟨?_,?_,?_⟩
  · intro v
    have hh:=graph_changed_comap_le P Q f v
    apply le_trans _ (hr (f v))
    exact_mod_cast hh
  · intro v
    have hh:=hrow' v
    apply le_trans _ (hrow (f v))
    exact_mod_cast hh
  · intro u
    have hh:=hcol' u
    apply le_trans _ (hcol (g u))
    exact_mod_cast hh
end Oberwolfach
