module

public import Oberwolfach.RootedEdgeChanges
public import Oberwolfach.FixedDomainTupleChanges

@[expose] public section

/-! Changed-edge counts on a fixed free-coordinate domain. Roots remain
ambient vertices and may lie outside that domain. Both endpoint maps are
fixed; the required degrees count their actual images of the free domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I V X:Type*} [Fintype I] [Fintype X] [DecidableEq I]

theorem rooted_edge_change_count_on_domain
    (e:X→V) (D:V→V→Prop) (delta:ℝ) (σ τ:Equiv.Perm V)
    (hout:∀ x,(∑ y:X,if D x (τ (e y)) then (1:ℝ) else 0)≤delta)
    (hin:∀ y,(∑ x:X,if D (σ (e x)) y then (1:ℝ) else 0)≤delta)
    (a b:V⊕I) (hab:RootedEdgeHasFreeEndpoint a b):
    (∑ f:I→X,if D (σ (rootedPositionValue (fun i=>e (f i)) a))
      (τ (rootedPositionValue (fun i=>e (f i)) b)) then (1:ℝ) else 0)≤
      (Fintype.card X:ℝ)^(Fintype.card I-1)*delta:=by
  cases a with
  | inl x=>
    cases b with
    | inl y=>exact hab.elim
    | inr j=>
      apply sum_bound_from_one_coordinate j
      intro g
      simp only [rootedPositionValue,Sum.elim_inl,Sum.elim_inr,id_eq,
        fillFreeCoordinate,dif_pos rfl,dite_true]
      exact hout (σ x)
  | inr i=>
    cases b with
    | inl y=>
      apply sum_bound_from_one_coordinate i
      intro g
      simp only [rootedPositionValue,Sum.elim_inl,Sum.elim_inr,id_eq,
        fillFreeCoordinate,dif_pos rfl,dite_true]
      exact hin (τ y)
    | inr j=>
      have hne:i≠j:=hab
      apply sum_bound_from_one_coordinate j
      intro g
      simp only [rootedPositionValue,Sum.elim_inr,fillFreeCoordinate,dif_pos rfl,dif_neg hne,dite_true]
      exact hout (σ (e (g ⟨i,hne⟩)))

variable [Fintype V] [DecidableEq V]

theorem fixedDomainTuple_edge_loss {J:Type*} [Fintype J]
    (A:Finset V) (P Q:(I→V)→Prop)
    (hP:∀ f,P f→∀ i,f i∈A) (hQ:∀ f,Q f→∀ i,f i∈A)
    (D:V→V→Prop) (delta:ℝ) (σ τ:J→Equiv.Perm V) (src dst:J→V⊕I)
    (hfree:∀ j,RootedEdgeHasFreeEndpoint (src j) (dst j))
    (hout:∀ j x,(∑ y:A,if D x (τ j y.val) then (1:ℝ) else 0)≤delta)
    (hin:∀ j y,(∑ x:A,if D (σ j x.val) y then (1:ℝ) else 0)≤delta)
    (hbad:∀ f,P f→¬Q f→∃ j,D (σ j (rootedPositionValue f (src j)))
      (τ j (rootedPositionValue f (dst j)))):
    (Fintype.card {f:I→V // P f}:ℝ)-Fintype.card {f:I→V // Q f}≤
      (Fintype.card J:ℝ)*delta*(A.card:ℝ)^(Fintype.card I-1):=by
  rw [Fintype.card_congr (fixedDomainTuplePredicateEquiv A P hP),
    Fintype.card_congr (fixedDomainTuplePredicateEquiv A Q hQ)]
  have hh:=finite_predicate_loss_union
    (fun f:I→A=>P (fun i=>(f i).val)) (fun f:I→A=>Q (fun i=>(f i).val))
    (fun j (f:I→A)=>D (σ j (rootedPositionValue (fun i=>(f i).val) (src j)))
      (τ j (rootedPositionValue (fun i=>(f i).val) (dst j))))
    (by intro f hp hq;exact hbad _ hp hq)
  apply hh.trans
  calc
    _ ≤∑ _j:J,(Fintype.card A:ℝ)^(Fintype.card I-1)*delta:=by
      apply Finset.sum_le_sum
      intro j _
      exact rooted_edge_change_count_on_domain (Subtype.val:A→V) D delta (σ j) (τ j)
        (hout j) (hin j) (src j) (dst j) (hfree j)
    _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe];ring

end Oberwolfach
