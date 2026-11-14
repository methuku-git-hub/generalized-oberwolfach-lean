module

public import Oberwolfach.OrdinaryWheelRemainders
public import Oberwolfach.GraphSelectionDegrees
public import Oberwolfach.OrdinaryDecompositionEdges

@[expose] public section
/-! Removing the protected inner pair creates only a controlled row imbalance
and leaves precisely the physical resources outside that pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_outer_host_balance (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card):
    ∀v,|((Q\spanningRestriction Q I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J))).card|≤(I.card:ℝ)+2*J.card:=by
  intro v
  let R:=spanningRestriction Q I
  let K:=fun v u=>H v u∧v∈I∧u∈J
  have hRQ:R≤Q:=by intro x y h;exact (spanningRestriction_adj Q I x y).mp h |>.1
  have hKH:∀v u,K v u→H v u:=by intro v u h;exact h.1
  have hRdeg:R.degree v≤I.card:=by
    rw [show R.degree v=_ from spanningRestriction_degree Q I v]
    split_ifs with hv
    · exact Finset.card_le_card Finset.inter_subset_right
    · omega
  have hKdeg:(Finset.univ.filter (K v)).card≤J.card:=by
    apply Finset.card_le_card
    intro u hu
    exact (Finset.mem_filter.mp hu).2.2.2
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
  have hb:(Q.degree v:ℝ)=2*(Finset.univ.filter (H v)).card:=by exact_mod_cast hbal v
  have hr:(R.degree v:ℝ)≤I.card:=by exact_mod_cast hRdeg
  have hk:((Finset.univ.filter (K v)).card:ℝ)≤J.card:=by exact_mod_cast hKdeg
  have hr0:(0:ℝ)≤R.degree v:=Nat.cast_nonneg _
  have hk0:(0:ℝ)≤(Finset.univ.filter (K v)).card:=Nat.cast_nonneg _
  have heH:(Finset.univ.filter (fun u=>H v u∧¬(v∈I∧u∈J)))=
      Finset.univ.filter (fun u=>H v u∧¬K v u):=by
    ext u;simp only [Finset.mem_filter,Finset.mem_univ,true_and,K];tauto
  rw [heH]
  change |((Q\R).degree v:ℝ)-2*(Finset.univ.filter (fun u=>H v u∧¬K v u)).card|≤_
  rw [heqR,heqH]
  apply abs_le.mpr
  constructor <;> linarith only [hb,hr,hk,hr0,hk0]

theorem ordinary_outer_host_resources (Q:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U):
    ordinaryHostResources (Q\spanningRestriction Q I) (fun v u=>H v u∧¬(v∈I∧u∈J))=
      ordinaryHostResources Q H\ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J):=by
  have he:(fun v u=>H v u∧¬(v∈I∧u∈J))=
      (fun v u=>H v u∧¬(H v u∧v∈I∧u∈J)):=by
    funext v u;apply propext;tauto
  rw [he,ordinaryHostResources_sdiff]
end Oberwolfach
