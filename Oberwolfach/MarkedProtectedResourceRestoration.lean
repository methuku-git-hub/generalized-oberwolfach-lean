module

public import Oberwolfach.MarkedInnerResources
public import Oberwolfach.MarkedIncidentResources

@[expose] public section

/-! The exact resource identity in the protected restoration step.
Only the prescribed inner correction and the active inner packing are
removed. Their effects on the deeper star and induced pair are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [DecidableEq V] [DecidableEq U]

def markedStarResource (T:Finset V) (W:Finset U):Finset V⊕(V×U)→Prop:=
  Sum.elim (fun e=>∃ v∈e,v∈T) (fun z=>z.1∈T∨z.2∈W)

theorem marked_active_inner_avoids_star
    (I T:Finset V) (J W:Finset U) (e:Finset V⊕(V×U))
    (he:markedInnerResource (I\T) (J\W) e):¬markedStarResource T W e:=by
  cases e with
  | inl e=>
    rintro ⟨v,hv,hT⟩
    exact (Finset.mem_sdiff.mp (he hv)).2 hT
  | inr z=>
    rintro (ht|hw)
    · exact (Finset.mem_sdiff.mp he.1).2 ht
    · exact (Finset.mem_sdiff.mp he.2).2 hw

theorem marked_protected_resource_restoration
    (FE FD FU E₀:Finset (Finset V⊕(V×U))) (I T:Finset V) (J W:Finset U)
    (hE:FE.filter (markedInnerResource I J)=E₀)
    (hD:FD.filter (markedInnerResource I J)=∅)
    (hU:FU.filter (markedInnerResource I J)=FU.filter (markedInnerResource (I\T) (J\W)))
    (hEU:Disjoint FE FU)
    (hstar:∀ e∈E₀,markedStarResource T W e)
    (hdeep:E₀.filter (markedInnerResource T W)=∅)
    (hpair:∀ e:Finset V,Sum.inl e∈FU→e.Nonempty):
    let A:=(FE∪FD∪FU).filter (markedInnerResource I J)
    A=E₀∪FU.filter (markedInnerResource (I\T) (J\W)) ∧
    Disjoint E₀ (FU.filter (markedInnerResource (I\T) (J\W))) ∧
    A.filter (markedStarResource T W)=E₀ ∧
    A.filter (markedInnerResource T W)=∅ ∧
    ∀ p:Finset V⊕(V×U)→Prop,
      (A.filter p).card≤(E₀.filter p).card+
        ((FU.filter (markedInnerResource (I\T) (J\W))).filter p).card:=by
  let B:=FU.filter (markedInnerResource (I\T) (J\W))
  have he:(FE∪FD∪FU).filter (markedInnerResource I J)=E₀∪B:=by
    rw [Finset.filter_union,Finset.filter_union,hE,hD,Finset.union_empty,hU]
  have hEB:Disjoint E₀ B:=by
    rw [←hE]
    exact hEU.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hBs:B.filter (markedStarResource T W)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨he,hs⟩:=Finset.mem_filter.mp he
    exact marked_active_inner_avoids_star I T J W e (Finset.mem_filter.mp he).2 hs
  have hBd:B.filter (markedInnerResource T W)=∅:=by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨he,hd⟩:=Finset.mem_filter.mp he
    obtain ⟨he,ha⟩:=Finset.mem_filter.mp he
    have hn:=marked_active_inner_avoids_star I T J W e ha
    cases e with
    | inl e=>
      obtain ⟨v,hv⟩:=hpair e he
      exact hn ⟨v,hv,hd hv⟩
    | inr z=>exact hn (Or.inl hd.1)
  refine ⟨he,hEB,?_,?_,?_⟩
  · rw [he,Finset.filter_union,hBs,Finset.union_empty]
    exact Finset.filter_eq_self.mpr hstar
  · rw [he,Finset.filter_union,hdeep,hBd,Finset.union_empty]
  · intro p
    rw [he,Finset.filter_union]
    exact Finset.card_union_le _ _

theorem marked_protected_restoration_margin
    (epsilon gamma sigma C xi nu N m:ℝ)
    (he:0<epsilon) (hN:0≤N) (hm:0≤m) (hC:0≤C) (hxi:0≤xi)
    (hgam:0≤gamma) (hsize:epsilon*N≤2*m)
    (hnu:nu=gamma*epsilon/200) (hcor:C*xi≤gamma/100) (hstar:C*xi≤sigma):
    C*xi*m+nu*N≤gamma*m/50∧C*xi*m≤sigma*m:=by
  have h1:C*xi*m≤gamma*m/100:=by nlinarith only [mul_le_mul_of_nonneg_right hcor hm]
  have h2:nu*N≤gamma*m/100:=by
    rw [hnu]
    nlinarith only [mul_le_mul_of_nonneg_left hsize hgam]
  exact ⟨by linarith only [h1,h2],mul_le_mul_of_nonneg_right hstar hm⟩

end Oberwolfach
