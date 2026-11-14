module

public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section
/-! Once reference spokes survive the complement embedding, row balance and
column counts control all additional remainder spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_reserved_spoke_change_bounds
    (Q Reference:SimpleGraph V) (H Href:V→U→Prop) (b e:ℝ) (target Uerr:U→ℝ)
    (hsub:∀v u,Href v u→H v u)
    (hbal:∀v,(Q.degree v:ℝ)=2*((Finset.univ.filter (H v)).card:ℝ))
    (hRim:∀v,(Q.degree v:ℝ)≤(Reference.degree v:ℝ)+b)
    (hRefRow:∀v,(Reference.degree v:ℝ)≤2*((Finset.univ.filter (Href v)).card:ℝ)+e)
    (hUpper:∀u,((Finset.univ.filter (fun v=>H v u)).card:ℝ)≤target u)
    (hLower:∀u,target u-Uerr u≤((Finset.univ.filter (fun v=>Href v u)).card:ℝ)):
    (∀v,2*((Finset.univ.filter (fun u=>H v u ∧ ¬Href v u)).card:ℝ)≤b+e) ∧
    (∀u,((Finset.univ.filter (fun v=>H v u ∧ ¬Href v u)).card:ℝ)≤Uerr u):=by
  constructor
  · intro v
    have hle:(Finset.univ.filter (Href v)).card≤(Finset.univ.filter (H v)).card:=by
      apply Finset.card_le_card
      intro u hu
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hu ⊢
      exact hsub v u hu
    have heq:((Finset.univ.filter (fun u=>H v u ∧ ¬Href v u)).card:ℝ)+
        ((Finset.univ.filter (Href v)).card:ℝ)=((Finset.univ.filter (H v)).card:ℝ):=by
      have hh:=spoke_row_sdiff_card H Href hsub v
      rw [hh]
      exact_mod_cast Nat.sub_add_cancel hle
    linarith [hbal v,hRim v,hRefRow v]
  · intro u
    have hle:(Finset.univ.filter (fun v=>Href v u)).card≤(Finset.univ.filter (fun v=>H v u)).card:=by
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hv ⊢
      exact hsub v u hv
    have heq:((Finset.univ.filter (fun v=>H v u ∧ ¬Href v u)).card:ℝ)+
        ((Finset.univ.filter (fun v=>Href v u)).card:ℝ)=
          ((Finset.univ.filter (fun v=>H v u)).card:ℝ):=by
      have hh:=spoke_col_sdiff_card H Href hsub u
      rw [hh]
      exact_mod_cast Nat.sub_add_cancel hle
    linarith [hUpper u,hLower u]
end Oberwolfach
