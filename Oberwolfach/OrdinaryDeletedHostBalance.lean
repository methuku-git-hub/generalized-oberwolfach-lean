module

public import Oberwolfach.OrdinaryWheelRemainders

@[expose] public section
/-! A bounded physical deletion changes the ordinary balance error by at
most its rim degree plus twice its spoke-row degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_deleted_host_balance
    (Q R:SimpleGraph V) (H K:V→U→Prop) (b dr ds:ℝ)
    (hRQ:R≤Q) (hKH:∀v u,K v u→H v u)
    (hbal:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤b)
    (hR:∀v,(R.degree v:ℝ)≤dr) (hK:∀v,((Finset.univ.filter (K v)).card:ℝ)≤ds):
    ∀v,|((Q\R).degree v:ℝ)-2*(Finset.univ.filter (fun u=>H v u∧¬K v u)).card|≤b+dr+2*ds:=by
  intro v
  have hRq:R.degree v≤Q.degree v:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree,←SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro w hw
    exact Q.mem_neighborFinset v w |>.mpr (hRQ ((R.mem_neighborFinset v w).mp hw))
  have hKs:(Finset.univ.filter (K v)).card≤(Finset.univ.filter (H v)).card:=by
    apply Finset.card_le_card
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hKH v u (Finset.mem_filter.mp hu).2⟩
  have heqR:((Q\R).degree v:ℝ)=(Q.degree v:ℝ)-R.degree v:=by
    rw [graph_degree_sdiff Q R hRQ v,Nat.cast_sub hRq]
  have heqH:((Finset.univ.filter (fun u=>H v u∧¬K v u)).card:ℝ)=
      (Finset.univ.filter (H v)).card-(Finset.univ.filter (K v)).card:=by
    have hh:=spoke_row_sdiff_card H K hKH v
    have hh':(Finset.univ.filter (fun u=>H v u∧¬K v u)).card=
        (Finset.univ.filter (H v)).card-(Finset.univ.filter (K v)).card:=by
      convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
    rw [hh',Nat.cast_sub hKs]
  rw [heqR,heqH]
  have hb:=abs_le.mp (hbal v)
  have hr0:(0:ℝ)≤R.degree v:=Nat.cast_nonneg _
  have hk0:(0:ℝ)≤(Finset.univ.filter (K v)).card:=Nat.cast_nonneg _
  apply abs_le.mpr
  constructor <;> linarith only [hb.1,hb.2,hR v,hK v,hr0,hk0]
end Oberwolfach
