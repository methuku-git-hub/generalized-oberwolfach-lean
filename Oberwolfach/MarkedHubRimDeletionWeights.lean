module

public import Oberwolfach.MarkedHubFixedWeightRestriction

@[expose] public section

/-! Degree error at a surviving hub after a rim deletion. The original
coefficients are restricted, not rebalanced or multiplied by a density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

theorem hub_marked_rim_deletion_weight_error (hm:3≤m) (hn:0<Fintype.card V)
    (u:U) (hdis:∀ v,¬(H₀ v u∧Hₖ v u)) (PE:E→Prop) (PK:K→Prop)
    (hinj:Function.Injective (fun e:E=>(tail e,head e)))
    (hkinj:Function.Injective (fun e:K=>(ktail e,khead e)))
    (w:MarkedCycleTuple tail head ktail khead m π b→ℝ) (B d:ℝ) (hB:0≤B) (hd:0≤d)
    (hw:∀ C,0≤w C∧w C≤B/(Fintype.card V:ℝ)^m)
    (hEout:∀ x,(∑ e,if ¬PE e∧tail e=x then (1:ℝ) else 0)≤d)
    (hEin:∀ x,(∑ e,if ¬PE e∧head e=x then (1:ℝ) else 0)≤d)
    (hKout:∀ x,(∑ e,if ¬PK e∧ktail e=x then (1:ℝ) else 0)≤d)
    (hKin:∀ x,(∑ e,if ¬PK e∧khead e=x then (1:ℝ) else 0)≤d)
    (v:V) (hv:H₀ v u∨Hₖ v u):
    |hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u)
      (fun C:HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀ Hₖ u=>
        w (markedCycleToLarger PE PK (hubCycleAsMarked u C))) v-
      hypergraphWeightedDegree (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=Hₖ) u) (fun C=>w (hubCycleAsMarked u C)) v|≤
      10*((m:ℝ)+1)^4*B*d/Fintype.card V:=by
  obtain ⟨j,hj⟩:∃ j:Bool,if j then Hₖ v u else H₀ v u:=by
    rcases hv with hv|hv
    · exact ⟨false,hv⟩
    · exact ⟨true,hv⟩
  rw [hub_marked_restricted_degree_eq_potential u hdis PE PK hinj hkinj w j v hj,
    hub_marked_degree_eq_potential u hdis w j v hj]
  let H:Bool→V→Unit→Prop:=fun j v _=>if j then Hₖ v u else H₀ v u
  have hout:∀ x,(∑ e,if ¬(True↔Sum.elim PE PK e)∧Sum.elim tail ktail e=x then (1:ℝ) else 0)≤2*d:=by
    intro x
    simp only [true_iff,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    have h1:=hEout x
    have h2:=hKout x
    linarith only [h1,h2]
  have hin:∀ x,(∑ e,if ¬(True↔Sum.elim PE PK e)∧Sum.elim head khead e=x then (1:ℝ) else 0)≤2*d:=by
    intro x
    simp only [true_iff,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]
    have h1:=hEin x
    have h2:=hKin x
    linarith only [h1,h2]
  have he:=typedMarkedPotentialLoad_spoke_degree_stability (H₀:=fun (_:V) (_:Unit)=>True)
    (Hₖ:=fun _ _=>True) hm hn (fun W=>w W.1) B hB (fun W=>hw W.1)
    (fun _=>True) (Sum.elim PE PK) H H (2*d) (by positivity) (by convert hout using 1 <;> congr!) (by convert hin using 1 <;> congr!)
    (by intro j x;simp only [iff_self,not_true_eq_false,bipAdj,ite_false,Finset.sum_const_zero];positivity)
    (by intro j x;simp only [iff_self,not_true_eq_false,bipAdj,ite_false,Finset.sum_const_zero];positivity) j v ()
  convert he using 1 <;> ring

end Oberwolfach
