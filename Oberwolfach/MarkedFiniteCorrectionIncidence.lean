module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedIncidentResources

@[expose] public section

/-! The sparse correction's auxiliary arc and spoke counts bound its
physical incidences. A physical marked head is charged at its inverse image
under the permutation; all ambient roots are retained. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_finite_correction_physical_incidence
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (δ:ℝ) (hδ:0≤δ)
    (hA:∀ v,((A.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ)
    (hV:∀ v,((S.filter (fun z=>z.1=v)).card:ℝ)≤δ)
    (hU:∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤δ)
    (x:V⊕U):
    (((markedFiniteResources tail head ktail khead π A S).filter (markedPhysicalIncident x)).card:ℝ)≤3*δ:=by
  have hArc (v:V):((A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)).card:ℝ)≤2*δ:=by
    let P:=fun v a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v
    have hsub:A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)⊆
        A.filter (P v)∪A.filter (P (π.symm v)):=by
      intro a ha
      obtain ⟨hmem,hi⟩:=Finset.mem_filter.mp ha
      cases a with
      | inl a=>
        apply Finset.mem_union.mpr;left
        exact Finset.mem_filter.mpr ⟨hmem,by simpa only [P,markedPhysicalEdge,Finset.mem_insert,Finset.mem_singleton,Sum.elim_inl,eq_comm] using hi⟩
      | inr a=>
        have hh:v=ktail a∨v=π (khead a):=by simpa only [markedPhysicalEdge,Sum.elim_inr,Finset.mem_insert,Finset.mem_singleton] using hi
        rcases hh with ht|hh
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hmem,Or.inl ht.symm⟩))
        · apply Finset.mem_union.mpr;right
          apply Finset.mem_filter.mpr;refine ⟨hmem,Or.inr ?_⟩
          change khead a=π.symm v
          rw [hh,π.symm_apply_apply]
    have hc:=(Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hr:=Nat.cast_le (α:=ℝ).mpr hc
    simp only [Nat.cast_add] at hr
    linarith only [hr,hA v,hA (π.symm v)]
  let AR:=A.image (fun a=>(Sum.inl (markedPhysicalEdge tail head ktail khead π a):Finset V⊕(V×U)))
  let SR:=S.image (Sum.inr:V×U→Finset V⊕(V×U))
  have hsum:(((markedFiniteResources tail head ktail khead π A S).filter (markedPhysicalIncident x)).card:ℝ)≤
      (AR.filter (markedPhysicalIncident x)).card+(SR.filter (markedPhysicalIncident x)).card:=by
    have hh:=Finset.card_union_le (AR.filter (markedPhysicalIncident x)) (SR.filter (markedPhysicalIncident x))
    rw [←Finset.filter_union] at hh
    exact_mod_cast hh
  cases x with
  | inl v=>
    have hr:((AR.filter (markedPhysicalIncident (Sum.inl v))).card:ℝ)≤2*δ:=by
      have hh:((AR.filter (markedPhysicalIncident (Sum.inl v))).card)≤(A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a)).card:=by
        dsimp only [AR];rw [Finset.filter_image]
        simpa only [markedPhysicalIncident,←Set.ncard_coe_finset,Finset.coe_filter] using
          (Finset.card_image_le (s:=A.filter (fun a=>v∈markedPhysicalEdge tail head ktail khead π a))
            (f:=fun a=>(Sum.inl (markedPhysicalEdge tail head ktail khead π a):Finset V⊕(V×U))))
      exact (Nat.cast_le.mpr hh).trans (hArc v)
    have hs:((SR.filter (markedPhysicalIncident (Sum.inl v))).card:ℝ)≤δ:=by
      have hh:(SR.filter (markedPhysicalIncident (Sum.inl v))).card≤(S.filter (fun z=>z.1=v)).card:=by
        dsimp only [SR];rw [Finset.filter_image]
        simpa only [markedPhysicalIncident,←Set.ncard_coe_finset,Finset.coe_filter] using
          (Finset.card_image_le (s:=S.filter (fun z=>z.1=v)) (f:=(Sum.inr:V×U→Finset V⊕(V×U))))
      exact (Nat.cast_le.mpr hh).trans (hV v)
    linarith only [hsum,hr,hs]
  | inr u=>
    have hr:(AR.filter (markedPhysicalIncident (Sum.inr u))).card=0:=by
      simp only [AR,Finset.filter_image,markedPhysicalIncident,Finset.filter_false,Finset.image_empty,Finset.card_empty]
    have hs:((SR.filter (markedPhysicalIncident (Sum.inr u))).card:ℝ)≤δ:=by
      have hh:(SR.filter (markedPhysicalIncident (Sum.inr u))).card≤(S.filter (fun z=>z.2=u)).card:=by
        dsimp only [SR];rw [Finset.filter_image]
        simpa only [markedPhysicalIncident,←Set.ncard_coe_finset,Finset.coe_filter] using
          (Finset.card_image_le (s:=S.filter (fun z=>z.2=u)) (f:=(Sum.inr:V×U→Finset V⊕(V×U))))
      exact (Nat.cast_le.mpr hh).trans (hU u)
    rw [hr,Nat.cast_zero,zero_add] at hsum
    linarith only [hsum,hs,hδ]

theorem marked_finite_correction_restricted_incidence
    (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (δ:ℝ) (hδ:0≤δ)
    (hA:∀ v,((A.filter (fun a=>Sum.elim tail ktail a=v∨Sum.elim head khead a=v)).card:ℝ)≤δ)
    (hV:∀ v,((S.filter (fun z=>z.1=v)).card:ℝ)≤δ)
    (hU:∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤δ)
    (p:Finset V⊕(V×U)→Prop) (x:V⊕U):
    ((((markedFiniteResources tail head ktail khead π A S).filter p).filter (markedPhysicalIncident x)).card:ℝ)≤3*δ:=by
  apply le_trans _ (marked_finite_correction_physical_incidence tail head ktail khead π A S δ hδ hA hV hU x)
  exact Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _)))

end Oberwolfach
