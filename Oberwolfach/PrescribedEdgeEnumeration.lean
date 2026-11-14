module

public import Oberwolfach.PrescribedPackingUnion
public import Oberwolfach.OrdinaryIncidentResources

@[expose] public section

/-! Enumerate an actual set of prescribed inner edges without identifying
unordered rim edges or counting their two orientations as different edges.
The input incidence bound gives all three indexed incidence bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finset_injective_enumeration {A:Type} [DecidableEq A] (S:Finset A):
    ∃ f:Fin S.card→A,Function.Injective f ∧ Finset.univ.image f=S:=by
  let f:Fin S.card→A:=fun i=>(S.equivFin.symm i).val
  refine ⟨f,Subtype.val_injective.comp S.equivFin.symm.injective,?_⟩
  ext a
  constructor
  · intro ha
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp ha
    exact (S.equivFin.symm i).property
  · intro ha
    exact Finset.mem_image.mpr ⟨S.equivFin ⟨a,ha⟩,Finset.mem_univ _,by simp [f]⟩

theorem prescribed_inner_edge_enumeration
    {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (Q F:SimpleGraph V) (H:V→U→Prop) (I:Finset V) (J:Finset U)
    (E:Finset (Sym2 V⊕(V×U))) (D:ℕ)
    (hE:E⊆ordinaryHostResources (spanningRestriction Q I) (fun v u=>H v u∧v∈I∧u∈J))
    (hF:∀ v w,Sum.inl s(v,w)∈E→¬F.Adj v w)
    (hD:∀ t,(E.filter (ordinaryResourceIncident t)).card≤D):
    ∃ Nr Ns:ℕ,∃ x y:Fin Nr→V,∃ z:Fin Ns→V,∃ u:Fin Ns→U,
      Nr+Ns=E.card ∧
      (∀ i,x i∈I) ∧ (∀ i,y i∈I) ∧ (∀ i,Q.Adj (x i) (y i)) ∧ (∀ i,¬F.Adj (x i) (y i)) ∧
      (∀ i j,i≠j→¬((x i=x j∧y i=y j)∨(x i=y j∧y i=x j))) ∧
      (∀ v,(Finset.univ.filter (fun i=>v=x i∨v=y i)).card≤D) ∧
      (∀ i,z i∈I) ∧ (∀ i,u i∈J) ∧ (∀ i,H (z i) (u i)) ∧
      Function.Injective (fun i=>(z i,u i)) ∧
      (∀ v,(Finset.univ.filter (fun i=>v=z i)).card≤D) ∧
      (∀ a,(Finset.univ.filter (fun i=>u i=a)).card≤D) ∧
      Finset.univ.image (Sum.elim (fun i=>Sum.inl s(x i,y i)) (fun i=>Sum.inr (z i,u i)))=E:=by
  let R:=Finset.univ.filter (fun e:Sym2 V=>Sum.inl e∈E)
  let S:=Finset.univ.filter (fun e:V×U=>Sum.inr e∈E)
  obtain ⟨f,hf,hfE⟩:=finset_injective_enumeration R
  obtain ⟨g,hg,hgE⟩:=finset_injective_enumeration S
  have hfmem (i:Fin R.card):Sum.inl (f i)∈E:=by
    have hh: f i∈R:=hfE ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    exact (Finset.mem_filter.mp hh).2
  have hgmem (i:Fin S.card):Sum.inr (g i)∈E:=by
    have hh:g i∈S:=hgE ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    exact (Finset.mem_filter.mp hh).2
  let x:=fun i=>(f i).out.1
  let y:=fun i=>(f i).out.2
  let z:=fun i=>(g i).1
  let u:=fun i=>(g i).2
  have hxy (i:Fin R.card):s(x i,y i)=f i:=by dsimp [x,y];rw [Sym2.mk];exact (f i).out_eq
  have hr (i:Fin R.card):Q.Adj (x i) (y i)∧x i∈I∧y i∈I:=by
    have he:=hE (hfmem i)
    rw [ordinaryHostResources_rim,←hxy i] at he
    exact (spanningRestriction_adj Q I (x i) (y i)).mp he
  have hs (i:Fin S.card):H (z i) (u i)∧z i∈I∧u i∈J:=
    (ordinaryHostResources_spoke (spanningRestriction Q I) _ (z i) (u i)).mp (hE (hgmem i))
  let e:Fin R.card⊕Fin S.card→Sym2 V⊕(V×U):=Sum.elim (fun i=>Sum.inl (f i)) (fun i=>Sum.inr (g i))
  have hei:Function.Injective e:=by
    intro i j he
    cases i with
    | inl i=>cases j with
      | inl j=>exact congrArg Sum.inl (hf (Sum.inl.inj he))
      | inr j=>exact (Sum.inl_ne_inr he).elim
    | inr i=>cases j with
      | inl j=>exact (Sum.inr_ne_inl he).elim
      | inr j=>exact congrArg Sum.inr (hg (Sum.inr.inj he))
  have heE:Finset.univ.image e=E:=by
    ext a
    cases a with
    | inl a=>
      constructor
      · intro ha
        obtain ⟨i,_,hi⟩:=Finset.mem_image.mp ha
        cases i with
        | inl i=>exact (Sum.inl.inj hi) ▸ hfmem i
        | inr i=>exact (Sum.inr_ne_inl hi).elim
      · intro ha
        have hh:a∈R:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
        obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp (hfE.symm ▸ hh)
        exact Finset.mem_image.mpr ⟨Sum.inl i,Finset.mem_univ _,rfl⟩
    | inr a=>
      constructor
      · intro ha
        obtain ⟨i,_,hi⟩:=Finset.mem_image.mp ha
        cases i with
        | inl i=>exact (Sum.inl_ne_inr hi).elim
        | inr i=>exact (Sum.inr.inj hi) ▸ hgmem i
      · intro ha
        have hh:a∈S:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
        obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp (hgE.symm ▸ hh)
        exact Finset.mem_image.mpr ⟨Sum.inr i,Finset.mem_univ _,rfl⟩
  refine ⟨R.card,S.card,x,y,z,u,?_,(fun i=>(hr i).2.1),(fun i=>(hr i).2.2),
    (fun i=>(hr i).1),(fun i=>hF _ _ ((hxy i).symm ▸ hfmem i)),?_,?_,
    (fun i=>(hs i).2.1),(fun i=>(hs i).2.2),(fun i=>(hs i).1),hg,?_,?_,?_⟩
  · have hh:=Finset.card_image_of_injective Finset.univ hei
    rw [heE] at hh
    simpa only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin] using hh.symm
  · intro i j hij hh
    apply hij
    apply hf
    rw [←hxy i,←hxy j]
    rcases hh with ⟨h1,h2⟩|⟨h1,h2⟩
    · rw [h1,h2]
    · rw [h1,h2,Sym2.eq_swap]
  · intro v
    apply le_trans _ (hD (Sum.inl v))
    apply Finset.card_le_card_of_injOn (fun i=>Sum.inl (f i))
    · intro i hi
      refine Finset.mem_filter.mpr ⟨hfmem i,?_⟩
      change v∈f i
      rw [←hxy i,Sym2.mem_iff]
      exact (Finset.mem_filter.mp hi).2
    · intro i _ j _ hij;exact hf (Sum.inl.inj hij)
  · intro v
    apply le_trans _ (hD (Sum.inl v))
    apply Finset.card_le_card_of_injOn (fun i=>Sum.inr (g i))
    · intro i hi
      exact Finset.mem_filter.mpr ⟨hgmem i,(Finset.mem_filter.mp hi).2⟩
    · intro i _ j _ hij;exact hg (Sum.inr.inj hij)
  · intro a
    apply le_trans _ (hD (Sum.inr a))
    apply Finset.card_le_card_of_injOn (fun i=>Sum.inr (g i))
    · intro i hi
      exact Finset.mem_filter.mpr ⟨hgmem i,(Finset.mem_filter.mp hi).2.symm⟩
    · intro i _ j _ hij;exact hg (Sum.inr.inj hij)
  · convert heE using 1
    congr 1
    funext i
    cases i with
    | inl i=>exact congrArg Sum.inl (hxy i)
    | inr i=>rfl

end Oberwolfach
