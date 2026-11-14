module

public import Oberwolfach.DirectedIncidenceSums

@[expose] public section

/-! Directed attachment cancellation. Incoming and outgoing attachment
bijections are separate, and the hub assignment is a permutation of all
rim incidences at the fixed row root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V E S:Type} [Fintype V] [Fintype E] [Fintype S]

 theorem marked_attachment_integer_identity
    (tail head:E→V) (row:S→V)
    (a:∀ v,{e:E // head e=v}≃{s:S // row s=v})
    (b:∀ v,{e:E // tail e=v}≃{s:S // row s=v})
    (σ:∀ v,Equiv.Perm (DirectedIncidence tail head v))
    (core rimIn rimOut:E→ℤ) (cross spokeIn spokeOut load:S→ℤ) (hub:E→V→ℤ):
    (∑ e,(core e+rimIn e+rimOut e+hub e (head e)+hub e (tail e)))+
    (∑ s,(cross s+spokeIn s+spokeOut s+load s))-
    (∑ v,∑ i:DirectedIncidence tail head v,
      ((Sum.elim (fun e:{e:E // head e=v}=>rimIn e.val) (fun e:{e:E // tail e=v}=>rimOut e.val)) i+
       (Sum.elim (fun e:{e:E // head e=v}=>spokeIn (a v e).val)
         (fun e:{e:E // tail e=v}=>spokeOut (b v e).val)) i+
       hub (directedIncidenceEdge (σ v i)) v))=
      (∑ e,core e)+(∑ s,cross s)+∑ s,load s:=by
  have hri:=finite_function_fiber_sum head rimIn
  have hro:=finite_function_fiber_sum tail rimOut
  have hsi:(∑ v,∑ e:{e:E // head e=v},spokeIn (a v e).val)=∑ s,spokeIn s:=by
    calc
      _ = ∑ v,∑ s:{s:S // row s=v},spokeIn s.val:=by
        apply Finset.sum_congr rfl
        intro v hv
        exact Equiv.sum_comp (a v) (fun s=>spokeIn s.val)
      _ = _:=finite_function_fiber_sum row spokeIn
  have hso:(∑ v,∑ e:{e:E // tail e=v},spokeOut (b v e).val)=∑ s,spokeOut s:=by
    calc
      _ = ∑ v,∑ s:{s:S // row s=v},spokeOut s.val:=by
        apply Finset.sum_congr rfl
        intro v hv
        exact Equiv.sum_comp (b v) (fun s=>spokeOut s.val)
      _ = _:=finite_function_fiber_sum row spokeOut
  have hh:(∑ v,∑ i:DirectedIncidence tail head v,hub (directedIncidenceEdge (σ v i)) v)=
      ∑ e,(hub e (head e)+hub e (tail e)):=by
    calc
      _ = ∑ v,∑ i:DirectedIncidence tail head v,hub (directedIncidenceEdge i) v:=by
        apply Finset.sum_congr rfl
        intro v hv
        exact Equiv.sum_comp (σ v) (fun i=>hub (directedIncidenceEdge i) v)
      _ = _:=directed_incidence_sum tail head hub
  simp_rw [Finset.sum_add_distrib] at hh ⊢
  rw [hh]
  have hsplit₁:(∑ v,∑ i:DirectedIncidence tail head v,
      (Sum.elim (fun e:{e:E // head e=v}=>rimIn e.val) (fun e:{e:E // tail e=v}=>rimOut e.val)) i)=
      (∑ e,rimIn e)+(∑ e,rimOut e):=by
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_add_distrib,hri,hro]
  have hsplit₂:(∑ v,∑ i:DirectedIncidence tail head v,
      (Sum.elim (fun e:{e:E // head e=v}=>spokeIn (a v e).val) (fun e:{e:E // tail e=v}=>spokeOut (b v e).val)) i)=
      (∑ s,spokeIn s)+(∑ s,spokeOut s):=by
    simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_add_distrib,hsi,hso]
  rw [hsplit₁,hsplit₂]
  abel

end Oberwolfach
