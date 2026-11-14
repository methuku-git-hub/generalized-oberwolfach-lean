module

public import Oberwolfach.OrdinaryDeletedHostBalanceRefined

@[expose] public section
/-! A reserve whose imbalance tracks a fraction of the parent imbalance
leaves an approximately balanced host without a full degree-size loss. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_balance_after_proportional_reserve (b z τ B e:ℝ)
    (hτ0:0≤τ) (hτ1:τ≤1) (hb:|b|≤B) (hz:|z-τ*b|≤e):
    |b-z|≤B+e:=by
  have hB:0≤B:=(abs_nonneg b).trans hb
  have ht0:0≤1-τ:=by linarith
  have ht1:1-τ≤1:=by linarith
  have hprod:|(1-τ)*b|≤B:=by
    rw [abs_mul,abs_of_nonneg ht0]
    calc
      (1-τ)*|b|≤(1-τ)*B:=mul_le_mul_of_nonneg_left hb ht0
      _≤B:=by nlinarith only [ht1,hB]
  calc
    |b-z|=|(1-τ)*b-(z-τ*b)|:=by congr 1;ring
    _≤|(1-τ)*b|+|z-τ*b|:=abs_sub _ _
    _≤B+e:=add_le_add hprod hz

theorem ordinary_deleted_host_balance_identity
    (Q R:SimpleGraph V) (H K:V→U→Prop) (hRQ:R≤Q) (hKH:∀v u,K v u→H v u) (v:V):
    ((Q\R).degree v:ℝ)-2*(Finset.univ.filter (fun u=>H v u∧¬K v u)).card=
      ((Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card)-
        ((R.degree v:ℝ)-2*(Finset.univ.filter (K v)).card):=by
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
  ring

theorem ordinary_proportional_reserve_balance
    (Q R:SimpleGraph V) (H K:V→U→Prop) (τ B e:ℝ)
    (hRQ:R≤Q) (hKH:∀v u,K v u→H v u) (hτ0:0≤τ) (hτ1:τ≤1)
    (hbal:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤B)
    (hreserve:∀v,|((R.degree v:ℝ)-2*(Finset.univ.filter (K v)).card)-
      τ*((Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card)|≤e):
    ∀v,|((Q\R).degree v:ℝ)-2*(Finset.univ.filter (fun u=>H v u∧¬K v u)).card|≤B+e:=by
  intro v
  rw [ordinary_deleted_host_balance_identity Q R H K hRQ hKH v]
  exact ordinary_balance_after_proportional_reserve _ _ τ B e hτ0 hτ1 (hbal v) (hreserve v)
end Oberwolfach
