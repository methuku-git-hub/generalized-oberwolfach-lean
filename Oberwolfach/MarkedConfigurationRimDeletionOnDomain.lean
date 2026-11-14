module

public import Oberwolfach.PhysicalDeletionOnDomain
public import Oberwolfach.MarkedConfigurationPathDeletion

@[expose] public section

/-! Configuration losses at the fixed free-coordinate domain scale.
The path roots stay ambient and their spoke conditions remain omitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_base_physical_rim_deletion_loss_on_domain
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (A T₀ TK:Finset V) (hT₀:T₀⊆A) (hTK:TK⊆A)
    (σ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (delta:ℝ)
    (hD:∀ b x,(∑ y:A,if D.Adj x (optionalSuccessor π b y.val) then (1:ℝ) else 0)≤delta):
    (Fintype.card {C:DenseMarkedBaseFamily P π (3*d) m T₀ TK //
      MarkedBaseRims P π (3*d) m (fun e=>σ (Sum.inl e)) C.val}:ℝ)-
    Fintype.card {C:DenseMarkedBaseFamily P π (3*d) m T₀ TK //
      MarkedBaseRims P π (3*d) m (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) C.val}≤
      ((m:ℝ)+1)*delta*(A.card:ℝ)^m:=by
  have hout (x:V):(∑ y:A,if D.Adj x y.val then (1:ℝ) else 0)≤delta:=by
    simpa only [optionalSuccessor,Bool.false_eq_true,ite_false] using hD false x
  have hshift (x:V):(∑ y:A,if D.Adj x (π y.val) then (1:ℝ) else 0)≤delta:=by
    simpa only [optionalSuccessor,ite_true] using hD true x
  have hin (y:V):(∑ x:A,if D.Adj x.val y then (1:ℝ) else 0)≤delta:=by
    simpa only [D.adj_comm] using hout y
  have hc (τ:Sym2 V→Option (Bool×Bool)):
      Fintype.card {C:DenseMarkedBaseFamily P π (3*d) m T₀ TK //MarkedBaseRims P π (3*d) m τ C.val}=
      Fintype.card {f:Fin (m+1)→A //DenseMarkedBase P π (3*d) T₀ TK (fun i=>(f i).val)∧MarkedBaseRims P π (3*d) m τ (fun i=>(f i).val)}:=by
    have he:=Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun f:Fin (m+1)→V=>DenseMarkedBase P π (3*d) T₀ TK f)
      (fun f=>MarkedBaseRims P π (3*d) m τ f))
    have hd:=Fintype.card_congr (fixedDomainTuplePredicateEquiv A
      (fun f:Fin (m+1)→V=>DenseMarkedBase P π (3*d) T₀ TK f∧MarkedBaseRims P π (3*d) m τ f) (by
      intro f hf i
      exact Fin.cases (hTK hf.1.2.1) (fun i=>hT₀ (hf.1.2.2.1 i)) i))
    exact he.trans hd
  rw [hc,hc]
  let bad:Fin m⊕Unit→(Fin (m+1)→A)→Prop
    | Sum.inl i,f=>D.Adj (f i.castSucc).val (f i.succ).val
    | Sum.inr _,f=>D.Adj (f (Fin.last m)).val (π (f 0).val)
  have hh:=finite_predicate_loss_union
    (fun f:Fin (m+1)→A=>DenseMarkedBase P π (3*d) T₀ TK (fun i=>(f i).val)∧MarkedBaseRims P π (3*d) m (fun e=>σ (Sum.inl e)) (fun i=>(f i).val))
    (fun f:Fin (m+1)→A=>DenseMarkedBase P π (3*d) T₀ TK (fun i=>(f i).val)∧MarkedBaseRims P π (3*d) m (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) (fun i=>(f i).val))
    bad (by
      intro f hf hn
      by_contra hnone
      apply hn
      refine ⟨hf.1,?_,?_⟩
      · intro i
        apply (markedPhysicalRim_delete_iff P π d σ D.edgeFinset false _ _).mpr
        refine ⟨hf.2.1 i,?_⟩
        intro he
        apply hnone
        exact ⟨Sum.inl i,by simpa only [bad,Bool.false_eq_true,ite_false,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he⟩
      · apply (markedPhysicalRim_delete_iff P π d σ D.edgeFinset true _ _).mpr
        refine ⟨hf.2.2,?_⟩
        intro he
        apply hnone
        exact ⟨Sum.inr (),by simpa only [bad,ite_true,SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he⟩)
  have hbound:(∑ j,∑ a,if bad j a then (1:ℝ) else 0)≤((m:ℝ)+1)*delta*(A.card:ℝ)^m:=by
    calc
      _ ≤∑ _i:Fin m⊕Unit,delta*(A.card:ℝ)^m:=by
        apply Finset.sum_le_sum
        intro i _
        cases i with
        | inl i=>
          have hne:i.castSucc≠i.succ:=by intro h;have he:=congrArg Fin.val h;simp at he
          have h:=rooted_edge_change_count_on_domain (Subtype.val:A→V) D.Adj delta
              (Equiv.refl V) (Equiv.refl V) hout hin
            (Sum.inr i.castSucc) (Sum.inr i.succ) hne
          simpa only [bad,rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,Fintype.card_coe,mul_comm] using h
        | inr i=>
          have hne:(Fin.last m:Fin (m+1))≠0:=by intro h;have he:=congrArg Fin.val h;simp at he;omega
          have h:=rooted_edge_change_count_on_domain (Subtype.val:A→V) D.Adj delta
              (Equiv.refl V) π hshift hin
            (Sum.inr (Fin.last m)) (Sum.inr (0:Fin (m+1))) hne
          simpa only [bad,rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,Fintype.card_coe,mul_comm] using h
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.cast_add,Nat.cast_one];ring
  simpa only [Fintype.card_eq_nat_card] using hh.trans hbound

end Oberwolfach
