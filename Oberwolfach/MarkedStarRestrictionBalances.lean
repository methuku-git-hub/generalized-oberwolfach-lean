module

public import Oberwolfach.MarkedFiniteDivisibilityOperations

@[expose] public section

/-! A temporarily reserved star has exactly the original incidences at
its specified rows and hubs. This gives the deep-vertex balances after
reservation; divisibility of the entire reserved star is not asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finite_restrict_filter_eq {X:Type} (A:Finset X) (p q:X→Prop) [DecidablePred p] [DecidablePred q]
    (h:∀ x∈A,q x→p x):
    (A.filter p).filter q=A.filter q:=by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · tauto
  · rintro ⟨hx,hq⟩;exact ⟨⟨hx,h x hx hq⟩,hq⟩

variable {V U E K:Type} [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {HK:V→U→Prop} {m:ℕ}

theorem marked_star_restriction_row_counts
    (A:Finset (E⊕K)) (S:Finset (V×U)) (T:Finset V) (W:Finset U) (v:V) (hv:v∈T):
    let KA:=A.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=S.filter (fun z=>z.1∈T∨z.2∈W)
    (KA.filter (fun a=>Sum.elim tail ktail a=v))=A.filter (fun a=>Sum.elim tail ktail a=v)∧
    (KA.filter (fun a=>Sum.elim head khead a=v))=A.filter (fun a=>Sum.elim head khead a=v)∧
    (KA.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true))=
      A.filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)∧
    (KS.filter (fun z=>z.1=v))=S.filter (fun z=>z.1=v)∧
    (KS.filter (fun z=>z.1=v∧HK z.1 z.2))=S.filter (fun z=>z.1=v∧HK z.1 z.2):=by
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply finite_restrict_filter_eq;intro a _ ha;exact Or.inl (ha.symm ▸ hv)
  · apply finite_restrict_filter_eq;intro a _ ha;exact Or.inr (ha.symm ▸ hv)
  · apply finite_restrict_filter_eq;intro a _ ha;exact Or.inr (ha.1.symm ▸ hv)
  · apply finite_restrict_filter_eq;intro z _ hz;exact Or.inl (hz.symm ▸ hv)
  · apply finite_restrict_filter_eq;intro z _ hz;exact Or.inl (hz.1.symm ▸ hv)

theorem marked_star_restriction_hub_counts
    (S:Finset (V×U)) (T:Finset V) (W:Finset U) (u:U) (hu:u∈W):
    let KS:=S.filter (fun z=>z.1∈T∨z.2∈W)
    (KS.filter (fun z=>z.2=u∧HK z.1 z.2))=S.filter (fun z=>z.2=u∧HK z.1 z.2)∧
    (KS.filter (fun z=>z.2=u∧¬HK z.1 z.2))=S.filter (fun z=>z.2=u∧¬HK z.1 z.2):=by
  constructor
  · apply finite_restrict_filter_eq;intro z _ hz;exact Or.inr (hz.1.symm ▸ hu)
  · apply finite_restrict_filter_eq;intro z _ hz;exact Or.inr (hz.1.symm ▸ hu)

theorem marked_remove_reserved_star_deep_balances
    (A C:Finset (E⊕K)) (S R:Finset (V×U))
    (hA:C⊆A) (hS:R⊆S)
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (hinner:MarkedRemainderDivisible tail head ktail khead HK C R m)
    (T:Finset V) (W:Finset U):
    let KA:=C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=R.filter (fun z=>z.1∈T∨z.2∈W)
    (∀ v∈T,
      ((A\KA).filter (fun a=>Sum.elim head khead a=v)).card=
        ((A\KA).filter (fun a=>Sum.elim tail ktail a=v)).card∧
      ((A\KA).filter (fun a=>Sum.elim head khead a=v)).card=((S\KS).filter (fun z=>z.1=v)).card∧
      ((A\KA).filter (fun a=>Sum.elim head khead a=v∧markedArcType a=true)).card=
        ((S\KS).filter (fun z=>z.1=v∧HK z.1 z.2)).card)∧
    (∀ u∈W,((S\KS).filter (fun z=>z.2=u∧¬HK z.1 z.2)).card=
      m*((S\KS).filter (fun z=>z.2=u∧HK z.1 z.2)).card):=by
  let KA:=C.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
  let KS:=R.filter (fun z=>z.1∈T∨z.2∈W)
  have hKA:KA⊆A:=(Finset.filter_subset _ _).trans hA
  have hKS:KS⊆S:=(Finset.filter_subset _ _).trans hS
  constructor
  · intro v hv
    obtain ⟨ht,hh,hm,hs,hsk⟩:=marked_star_restriction_row_counts (HK:=HK) C R T W v hv
    refine ⟨?_,?_,?_⟩
    · rw [finite_filter_sdiff_card A KA hKA,finite_filter_sdiff_card A KA hKA,ht,hh,hdiv.directed v,hinner.directed v]
    · rw [finite_filter_sdiff_card A KA hKA,finite_filter_sdiff_card S KS hKS,hh,hs,hdiv.row v,hinner.row v]
    · rw [finite_filter_sdiff_card A KA hKA,finite_filter_sdiff_card S KS hKS,hm,hsk,hdiv.marked v,hinner.marked v]
  · intro u hu
    obtain ⟨hk,h0⟩:=marked_star_restriction_hub_counts (HK:=HK) R T W u hu
    rw [finite_filter_sdiff_card S KS hKS,finite_filter_sdiff_card S KS hKS,hk,h0,
      hdiv.hub u,hinner.hub u,Nat.mul_sub_left_distrib]

end Oberwolfach
