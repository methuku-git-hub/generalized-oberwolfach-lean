module

public import Oberwolfach.SupportedBoundedFactors
public import Oberwolfach.EmbeddedFiniteSets

@[expose] public section

/-! Bounded two factors on an actual fixed vertex domain. The ambient
candidate identifiers, original coefficients and canonical edge pairs are
preserved by the temporary one-class coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem single_class_bounded_factors (r J:ℕ) (hr:3≤r) (hJ:1≤J)
    (S:Tpl→VertexAbsorberTemplate r) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
      ∀ (W C:Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      ∀ (T:Finset W) (R:C→Finset W) (w:C→ℝ),(T.card:ℝ)=r*k→
      (∀ C₀,R C₀⊆T)→(∀ C₀,(R C₀).card=r)→
      (∀ Y:Finset W,Fintype.card {C₀:C // R C₀=Y}≤J)→
      (∀ C₀,b/k^(r-1)≤w C₀ ∧ w C₀≤B/k^(r-1))→
      (∀ v∈T,|1-hypergraphWeightedDegree R w v|≤η)→
      (∀ X:Finset W,X⊆T→X.card=r→α*k^(r*r)≤Fintype.card (LabelledAbsorberFamily R S X))→
      ∀ (I Z:Finset W) (z:ℕ),(I.card:ℝ)≤F₀→Z⊆T→Z.card=r*z→z≤q→
      ∀ E:Finset (W×W),(∀ p∈E,p.1≠p.2)→(E.card:ℝ)≤D*k→
      ∀ P:C→Finset (W×W),(∀ C₀,∀ p∈P C₀,p.1≠p.2∧p.1∈R C₀∧p.2∈R C₀)→
      (∀ C₀,(P C₀).card≤r)→(∀ C₀ v,((P C₀).filter (fun p=>v=p.1∨v=p.2)).card≤2)→
      ∃ A:Finset W,∃ D₀ D₁:Finset C,A⊆T ∧ Disjoint A (Z∪I) ∧ A.card=r*t ∧
        (∀ p∈E,¬(p.1∈A∧p.2∈A)) ∧
        ((∀ x∈D₀,∀ y∈D₀,x≠y→Disjoint (R x) (R y)) ∧ D₀.biUnion R=A) ∧
        ((∀ x∈D₁,∀ y∈D₁,x≠y→Disjoint (R x) (R y)) ∧ D₁.biUnion R=A∪Z) ∧
        Disjoint (D₀.biUnion P) (D₁.biUnion P) ∧ ∀ C₀∈D₁,(R C₀∩Z).card≤1:=by
  obtain ⟨η,hη,hbase⟩:=supported_bounded_factors (s:=1) (by omega) (fun _=>r) r J hr hJ
    (fun _=>by omega) (by simp) S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ D hF₀ hD
  refine ⟨k₀,hk₀,?_⟩
  intro k hk W C _ _ _ _ T R w hT hsupp hR hmult hw herr habs I Z z hI hZT hZ hz E hE hEc P hP hPc hPd
  let V:Fin 1→Type:=fun _=>T
  let e:(Σ i,V i)↪W:=⟨fun v=>v.2.val,by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    have hij:i=j:=Subsingleton.elim _ _
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext h)⟩
  let ep:((Σ i,V i)×(Σ i,V i))↪(W×W):=
    ⟨fun p=>(e p.1,e p.2),by intro p q h;exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))⟩
  have hsupported (C₀:C) (v:W) (hv:v∈R C₀):∃ x,e x=v:=⟨⟨0,⟨v,hsupp C₀ hv⟩⟩,rfl⟩
  have hclass (Y:Finset W) (hY:Y⊆T) (i:Fin 1):
      (Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈Y)).card=Y.card:=by
    apply Finset.card_bij (fun v _=>v.val)
    · intro v hv;exact (Finset.mem_filter.mp hv).2
    · intro v _ w _ h;exact Subtype.ext h
    · intro v hv;exact ⟨⟨v,hY hv⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hPimage (C₀:C):(embeddedPreimage ep (P C₀)).image ep=P C₀:=by
    apply embeddedPreimage_image
    intro p hp
    exact ⟨(⟨0,⟨p.1,hsupp C₀ (hP C₀ p hp).2.1⟩⟩,⟨0,⟨p.2,hsupp C₀ (hP C₀ p hp).2.2⟩⟩),rfl⟩
  let I':=embeddedPreimage e I
  let Z':=embeddedPreimage e Z
  let E':=embeddedPreimage ep E
  let P':=fun C₀=>embeddedPreimage ep (P C₀)
  have hZimage:Z'.image e=Z:=embeddedPreimage_image e Z (fun v hv=>⟨⟨0,⟨v,hZT hv⟩⟩,rfl⟩)
  have hIbound:(I'.card:ℝ)≤F₀:=by
    apply le_trans _ hI
    exact_mod_cast (show I'.card≤I.card from Finset.card_le_card_of_injOn e
      (fun v hv=>(embeddedPreimage_mem e I v).mp hv) (fun _ _ _ _ h=>e.injective h))
  have hEbound:(E'.card:ℝ)≤D*k:=by
    apply le_trans _ hEc
    exact_mod_cast (show E'.card≤E.card from Finset.card_le_card_of_injOn ep
      (fun p hp=>(embeddedPreimage_mem ep E p).mp hp) (fun _ _ _ _ h=>ep.injective h))
  have hPcard (C₀:C):(P' C₀).card≤r:=by
    have hc:=congrArg Finset.card (hPimage C₀)
    rw [Finset.card_image_of_injective _ ep.injective] at hc
    exact hc.trans_le (hPc C₀)
  have hPdeg (C₀:C) (v:Σ i,V i):((P' C₀).filter (fun p=>v=p.1∨v=p.2)).card≤2:=by
    apply le_trans _ (hPd C₀ (e v))
    apply Finset.card_le_card_of_injOn ep
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hvp⟩
      refine Finset.mem_filter.mpr ⟨(embeddedPreimage_mem ep (P C₀) p).mp hp,?_⟩
      exact hvp.elim (fun h=>Or.inl (congrArg e h)) (fun h=>Or.inr (congrArg e h))
    · intro _ _ _ _ h;exact ep.injective h
  obtain ⟨A,M₀,M₁,hAZ,hA,hAE,hM₀,hM₁,hdis,hcap⟩:=hbase k hk V W C e R w
    (fun _=>by simpa only [V,Fintype.card_coe] using hT) hsupported
    (fun C₀ i=>(hclass (R C₀) (hsupp C₀) i).trans (hR C₀)) hmult hw
    (fun v=>herr _ v.2.property) (by
      intro σ
      apply habs
      · intro v hv;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv;exact x.2.property
      · rw [Finset.card_image_of_injective _ e.injective,profileRootSet_card];simp)
    I' Z' z hIbound hz (fun i=>by
      simpa only [Z',embeddedPreimage_mem] using (hclass Z hZT i).trans hZ)
    E' (fun p hp h=>hE (ep p) ((embeddedPreimage_mem ep E p).mp hp) (congrArg e h)) hEbound P'
    (fun C₀ p hp=>⟨fun he=>(hP C₀ (ep p) ((embeddedPreimage_mem ep (P C₀) p).mp hp)).1 (congrArg e he),
      (hP C₀ (ep p) ((embeddedPreimage_mem ep (P C₀) p).mp hp)).2⟩) hPcard hPdeg
  have hAc:A.card=r*t:=by
    rw [sigma_finset_card]
    simp_rw [hA]
    simp
  have hdisP:Disjoint (M₀.biUnion P) (M₁.biUnion P):=by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨C₀,hC₀,hp⟩:=Finset.mem_biUnion.mp hp
    obtain ⟨C₁,hC₁,hq⟩:=Finset.mem_biUnion.mp hq
    obtain ⟨p',hp',he⟩:=Finset.mem_image.mp ((hPimage C₀).symm ▸ hp)
    have hq':p'∈P' C₁:=(embeddedPreimage_mem ep (P C₁) p').mpr (he.symm ▸ hq)
    exact Finset.disjoint_left.mp hdis (Finset.mem_biUnion.mpr ⟨C₀,hC₀,hp'⟩)
      (Finset.mem_biUnion.mpr ⟨C₁,hC₁,hq'⟩)
  refine ⟨A.image e,M₀,M₁,?_,?_,?_,?_,hM₀,?_,hdisP,?_⟩
  · intro v hv;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv;exact x.2.property
  · apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    apply Finset.disjoint_left.mp hAZ hx
    rcases Finset.mem_union.mp hv' with hz|hi
    · exact Finset.mem_union_left _ ((embeddedPreimage_mem e Z x).mpr hz)
    · exact Finset.mem_union_right _ ((embeddedPreimage_mem e I x).mpr hi)
  · rw [Finset.card_image_of_injective _ e.injective,hAc]
  · intro p hp hpa
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hpa.1
    obtain ⟨y,hy,hyv⟩:=Finset.mem_image.mp hpa.2
    have hep:ep (x,y)=p:=Prod.ext hxv hyv
    exact hAE (x,y) ((embeddedPreimage_mem ep E (x,y)).mpr (hep.symm ▸ hp)) ⟨hx,hy⟩
  · simpa only [Finset.image_union,hZimage] using hM₁
  · simpa only [hZimage] using hcap

end Oberwolfach
