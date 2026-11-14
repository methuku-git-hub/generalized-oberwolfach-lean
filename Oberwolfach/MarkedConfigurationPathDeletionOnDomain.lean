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

theorem marked_path_physical_rim_deletion_loss_on_domain
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (j:Bool) (v v':V) (A T₀ TK:Finset V) (hT₀:T₀⊆A) (hTK:TK⊆A)
    (σ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (delta:ℝ)
    (hD:∀ b x,(∑ y:A,if D.Adj x (optionalSuccessor π b y.val) then (1:ℝ) else 0)≤delta):
    (Fintype.card {C:DenseRootMarkedPathFamily P π (3*d) m j T₀ TK v v' //
      MarkedPathRims P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) C.val}:ℝ)-
    Fintype.card {C:DenseRootMarkedPathFamily P π (3*d) m j T₀ TK v v' //
      MarkedPathRims P π (3*d) m j v v' (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) C.val}≤
      ((m:ℝ)+4)*delta*(A.card:ℝ)^m:=by
  have hout (x:V):(∑ y:A,if D.Adj x y.val then (1:ℝ) else 0)≤delta:=by
    simpa only [optionalSuccessor,Bool.false_eq_true,ite_false] using hD false x
  have hshift (x:V):(∑ y:A,if D.Adj x (π y.val) then (1:ℝ) else 0)≤delta:=by
    simpa only [optionalSuccessor,ite_true] using hD true x
  have hin (y:V):(∑ x:A,if D.Adj x.val y then (1:ℝ) else 0)≤delta:=by
    simpa only [D.adj_comm] using hout y
  have hc (τ:Sym2 V→Option (Bool×Bool)):
      Fintype.card {C:DenseRootMarkedPathFamily P π (3*d) m j T₀ TK v v' //MarkedPathRims P π (3*d) m j v v' τ C.val}=
      Fintype.card {f:Fin (m+1)→A //DenseRootMarkedPath P π (3*d) j T₀ TK v v' (fun i=>(f i).val)∧MarkedPathRims P π (3*d) m j v v' τ (fun i=>(f i).val)}:=by
    have he:=Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun f:Fin (m+1)→V=>DenseRootMarkedPath P π (3*d) j T₀ TK v v' f)
      (fun f=>MarkedPathRims P π (3*d) m j v v' τ f))
    have hd:=Fintype.card_congr (fixedDomainTuplePredicateEquiv A
      (fun f:Fin (m+1)→V=>DenseRootMarkedPath P π (3*d) j T₀ TK v v' f∧MarkedPathRims P π (3*d) m j v v' τ f) (by
      intro f hf i
      have hi:=hf.1.2.2.1 i
      split_ifs at hi
      · exact hTK hi
      · exact hT₀ hi))
    exact he.trans hd
  rw [hc,hc]
  let bad:=fun (i:Fin m⊕(Bool×Bool)) (f:Fin (m+1)→A)=>
    D.Adj (pathPhysicalTail v v' (fun i=>(f i).val) i) (pathPhysicalHead π j v v' (fun i=>(f i).val) i)
  have hh:=finite_predicate_loss_union
    (fun f:Fin (m+1)→A=>DenseRootMarkedPath P π (3*d) j T₀ TK v v' (fun i=>(f i).val)∧MarkedPathRims P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) (fun i=>(f i).val))
    (fun f:Fin (m+1)→A=>DenseRootMarkedPath P π (3*d) j T₀ TK v v' (fun i=>(f i).val)∧MarkedPathRims P π (3*d) m j v v' (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) (fun i=>(f i).val))
    bad (by
      intro f hf hn
      by_contra hnone
      apply hn
      refine ⟨hf.1,?_⟩
      intro i
      apply (markedPhysicalRim_delete_iff P π d σ D.edgeFinset _ _ _).mpr
      refine ⟨hf.2 i,?_⟩
      intro he
      apply hnone
      refine ⟨i,?_⟩
      have he':D.Adj (pathPhysicalTail v v' (fun i=>(f i).val) i)
          (optionalSuccessor π (pathPositionType m j i) (pathAuxiliaryHead m v v' (fun i=>(f i).val) i)):=by
        simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,optionalSuccessor] using he
      dsimp only [bad]
      rw [pathPhysicalHead_auxiliary]
      exact he')
  have hbound:(∑ i,∑ f,if bad i f then (1:ℝ) else 0)≤((m:ℝ)+4)*delta*(A.card:ℝ)^m:=by
    calc
      _ ≤∑ _i:Fin m⊕(Bool×Bool),delta*(A.card:ℝ)^m:=by
        apply Finset.sum_le_sum
        intro i _
        cases i with
        | inl i=>
          have hne:i.castSucc≠i.succ:=by intro h;have he:=congrArg Fin.val h;simp at he
          cases ht:pathInternalType j i
          · have h:=rooted_edge_change_count_on_domain (Subtype.val:A→V) D.Adj delta
              (Equiv.refl V) (Equiv.refl V) hout hin
              (Sum.inr i.castSucc) (Sum.inr i.succ) hne
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,ht,optionalSuccessor,Bool.false_eq_true,ite_false,
              rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,Fintype.card_coe,mul_comm] using h
          · have h:=rooted_edge_change_count_on_domain (Subtype.val:A→V) D.Adj delta
              (Equiv.refl V) π hshift hin
              (Sum.inr i.castSucc) (Sum.inr i.succ) hne
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,ht,optionalSuccessor,ite_true,
              rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,Fintype.card_coe,mul_comm] using h
        | inr i=>
          obtain ⟨closing,side⟩:=i
          cases closing
          · have h:=rooted_edge_change_count_on_domain (Subtype.val:A→V) D.Adj delta
              (Equiv.refl V) (Equiv.refl V) hout hin
              (Sum.inl (if side then v' else v)) (Sum.inr (0:Fin (m+1))) (by trivial)
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,Bool.false_eq_true,ite_false,
              rootedPositionValue,Sum.elim_inr,Sum.elim_inl,id_eq,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,Fintype.card_coe,mul_comm] using h
          · have h:=rooted_edge_change_count_on_domain (Subtype.val:A→V) D.Adj delta
              (Equiv.refl V) (Equiv.refl V) hout hin
              (Sum.inr (Fin.last m)) (Sum.inl (optionalSuccessor π j (if side then v' else v)))
              (by trivial)
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,ite_true,
              rootedPositionValue,Sum.elim_inr,Sum.elim_inl,id_eq,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,Fintype.card_coe,mul_comm] using h
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat];ring
  simpa only [Fintype.card_eq_nat_card] using hh.trans hbound

end Oberwolfach
