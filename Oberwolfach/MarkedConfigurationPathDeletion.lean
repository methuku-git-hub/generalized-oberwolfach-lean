module

public import Oberwolfach.MarkedConfigurationRimDeletion

@[expose] public section

/-! The actual common-path count after physical rim deletion. Every
physical edge has a free endpoint, including the four edges incident
with the two fixed roots; no spoke condition is imposed at those roots. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem marked_path_physical_rim_deletion_loss
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (j:Bool) (v v':V) (T₀ TK:Finset V)
    (σ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (delta:ℝ)
    (hD:∀ x,(D.degree x:ℝ)≤delta):
    (Fintype.card {C:DenseRootMarkedPathFamily P π (3*d) m j T₀ TK v v' //
      MarkedPathRims P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) C.val}:ℝ)-
    Fintype.card {C:DenseRootMarkedPathFamily P π (3*d) m j T₀ TK v v' //
      MarkedPathRims P π (3*d) m j v v' (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) C.val}≤
      ((m:ℝ)+4)*delta*(Fintype.card V:ℝ)^m:=by
  obtain ⟨hout,hin⟩:=physical_deletion_degree_sum D delta hD
  have hc (τ:Sym2 V→Option (Bool×Bool)):
      Fintype.card {C:DenseRootMarkedPathFamily P π (3*d) m j T₀ TK v v' //MarkedPathRims P π (3*d) m j v v' τ C.val}=
      Fintype.card {f:Fin (m+1)→V //DenseRootMarkedPath P π (3*d) j T₀ TK v v' f∧MarkedPathRims P π (3*d) m j v v' τ f}:=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  rw [hc,hc]
  let bad:=fun (i:Fin m⊕(Bool×Bool)) (f:Fin (m+1)→V)=>
    D.Adj (pathPhysicalTail v v' f i) (pathPhysicalHead π j v v' f i)
  have hh:=finite_predicate_loss_union
    (fun f:Fin (m+1)→V=>DenseRootMarkedPath P π (3*d) j T₀ TK v v' f∧MarkedPathRims P π (3*d) m j v v' (fun e=>σ (Sum.inl e)) f)
    (fun f:Fin (m+1)→V=>DenseRootMarkedPath P π (3*d) j T₀ TK v v' f∧MarkedPathRims P π (3*d) m j v v' (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) f)
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
      have he':D.Adj (pathPhysicalTail v v' f i)
          (optionalSuccessor π (pathPositionType m j i) (pathAuxiliaryHead m v v' f i)):=by
        simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet,optionalSuccessor] using he
      dsimp only [bad]
      rw [pathPhysicalHead_auxiliary]
      exact he')
  have hbound:(∑ i,∑ f,if bad i f then (1:ℝ) else 0)≤((m:ℝ)+4)*delta*(Fintype.card V:ℝ)^m:=by
    calc
      _ ≤∑ _i:Fin m⊕(Bool×Bool),delta*(Fintype.card V:ℝ)^m:=by
        apply Finset.sum_le_sum
        intro i _
        cases i with
        | inl i=>
          have hne:i.castSucc≠i.succ:=by intro h;have he:=congrArg Fin.val h;simp at he
          cases ht:pathInternalType j i
          · have h:=rooted_edge_change_count D.Adj delta hout hin
              (Sum.inr i.castSucc) (Sum.inr i.succ) hne (Equiv.refl V) (Equiv.refl V)
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,ht,optionalSuccessor,Bool.false_eq_true,ite_false,
              rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,mul_comm] using h
          · have h:=rooted_edge_change_count D.Adj delta hout hin
              (Sum.inr i.castSucc) (Sum.inr i.succ) hne (Equiv.refl V) π
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,ht,optionalSuccessor,ite_true,
              rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,mul_comm] using h
        | inr i=>
          obtain ⟨closing,side⟩:=i
          cases closing
          · have h:=rooted_edge_change_count D.Adj delta hout hin
              (Sum.inl (if side then v' else v)) (Sum.inr (0:Fin (m+1))) (by trivial) (Equiv.refl V) (Equiv.refl V)
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,Bool.false_eq_true,ite_false,
              rootedPositionValue,Sum.elim_inr,Sum.elim_inl,id_eq,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,mul_comm] using h
          · have h:=rooted_edge_change_count D.Adj delta hout hin
              (Sum.inr (Fin.last m)) (Sum.inl (optionalSuccessor π j (if side then v' else v)))
              (by trivial) (Equiv.refl V) (Equiv.refl V)
            simpa only [bad,pathPhysicalTail,pathPhysicalHead,ite_true,
              rootedPositionValue,Sum.elim_inr,Sum.elim_inl,id_eq,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,mul_comm] using h
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat];ring
  simpa only [Fintype.card_eq_nat_card] using hh.trans hbound

end Oberwolfach
