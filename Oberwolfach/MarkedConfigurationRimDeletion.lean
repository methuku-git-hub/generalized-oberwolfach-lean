module

public import Oberwolfach.MarkedSampleDeletedArcs
public import Oberwolfach.MarkedConfigurationSpokeChanges
public import Oberwolfach.RootedEdgeChanges
public import Oberwolfach.TupleRelationDeletionCounts

@[expose] public section

/-! Loss of actual local cycle and rooted-path candidates under a later
physical rim deletion. The two path roots remain fixed and external roots
are allowed. Counts use their original free-coordinate scale. -/
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

theorem physical_deletion_degree_sum (D:SimpleGraph V) (delta:ℝ)
    (hD:∀ x,(D.degree x:ℝ)≤delta):
    (∀ x,(∑ y:V,if D.Adj x y then (1:ℝ) else 0)≤delta) ∧
    (∀ y,(∑ x:V,if D.Adj x y then (1:ℝ) else 0)≤delta):=by
  have he (x:V):(∑ y:V,if D.Adj x y then (1:ℝ) else 0)=D.degree x:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree,SimpleGraph.neighborFinset_eq_filter]
    simp only [Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  refine ⟨fun x=>(he x).trans_le (hD x),?_⟩
  intro y
  simpa only [D.adj_comm] using (he y).trans_le (hD y)

theorem marked_base_physical_rim_deletion_loss
    (P:SimpleGraph V) (π:Equiv.Perm V) (d m:ℕ) (hm:1≤m) (T₀ TK:Finset V)
    (σ:RawMarkedOutcome V U Γ Color) (D:SimpleGraph V) (delta:ℝ)
    (hD:∀ x,(D.degree x:ℝ)≤delta):
    (Fintype.card {C:DenseMarkedBaseFamily P π (3*d) m T₀ TK //
      MarkedBaseRims P π (3*d) m (fun e=>σ (Sum.inl e)) C.val}:ℝ)-
    Fintype.card {C:DenseMarkedBaseFamily P π (3*d) m T₀ TK //
      MarkedBaseRims P π (3*d) m (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) C.val}≤
      ((m:ℝ)+1)*delta*(Fintype.card V:ℝ)^m:=by
  obtain ⟨hout,hin⟩:=physical_deletion_degree_sum D delta hD
  have hc (τ:Sym2 V→Option (Bool×Bool)):
      Fintype.card {C:DenseMarkedBaseFamily P π (3*d) m T₀ TK //MarkedBaseRims P π (3*d) m τ C.val}=
      Fintype.card {f:Fin (m+1)→V //DenseMarkedBase P π (3*d) T₀ TK f∧MarkedBaseRims P π (3*d) m τ f}:=
    Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  rw [hc,hc]
  let bad:Fin m⊕Unit→(Fin (m+1)→V)→Prop
    | Sum.inl i,f=>D.Adj (f i.castSucc) (f i.succ)
    | Sum.inr _,f=>D.Adj (f (Fin.last m)) (π (f 0))
  have hh:=finite_predicate_loss_union
    (fun f:Fin (m+1)→V=>DenseMarkedBase P π (3*d) T₀ TK f∧MarkedBaseRims P π (3*d) m (fun e=>σ (Sum.inl e)) f)
    (fun f:Fin (m+1)→V=>DenseMarkedBase P π (3*d) T₀ TK f∧MarkedBaseRims P π (3*d) m (fun e=>rawMarkedDeleteRims σ D.edgeFinset (Sum.inl e)) f)
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
  have hbound:(∑ j,∑ a,if bad j a then (1:ℝ) else 0)≤((m:ℝ)+1)*delta*(Fintype.card V:ℝ)^m:=by
    calc
      _ ≤∑ _i:Fin m⊕Unit,delta*(Fintype.card V:ℝ)^m:=by
        apply Finset.sum_le_sum
        intro i _
        cases i with
        | inl i=>
          have hne:i.castSucc≠i.succ:=by intro h;have he:=congrArg Fin.val h;simp at he
          have h:=rooted_edge_change_count D.Adj delta hout hin
            (Sum.inr i.castSucc) (Sum.inr i.succ) hne (Equiv.refl V) (Equiv.refl V)
          simpa only [bad,rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,mul_comm] using h
        | inr i=>
          have hne:(Fin.last m:Fin (m+1))≠0:=by intro h;have he:=congrArg Fin.val h;simp at he;omega
          have h:=rooted_edge_change_count D.Adj delta hout hin
            (Sum.inr (Fin.last m)) (Sum.inr (0:Fin (m+1))) hne (Equiv.refl V) π
          simpa only [bad,rootedPositionValue,Sum.elim_inr,Equiv.refl_apply,Fintype.card_fin,Nat.add_sub_cancel,mul_comm] using h
      _ = _:=by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_sum,Fintype.card_fin,Fintype.card_unit,Nat.cast_add,Nat.cast_one];ring
  simpa only [Fintype.card_eq_nat_card] using hh.trans hbound

end Oberwolfach
