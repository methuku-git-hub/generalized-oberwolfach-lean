module

public import Oberwolfach.SupportedBoundedFactors
public import Oberwolfach.EmbeddedFiniteSets

@[expose] public section

/-! The bounded two-factor construction on fixed disjoint ambient classes.
The candidate identifiers, original weights and directed endpoint pairs
are retained under the temporary sigma coordinates. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

 theorem fixed_class_bounded_factors (s:ℕ) (hs:1≤s) (a:Fin s→ℕ) (c J:ℕ)
    (hc:3≤c) (hJ:1≤J) (ha:∀ i,1≤a i) (has:∑ i,a i=c)
    (S:Tpl→VertexAbsorberTemplate c) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
      ∀ (W C:Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      ∀ (T:Fin s→Finset W) (R:C→Finset W) (w:C→ℝ),
      (∀ i j,i≠j→Disjoint (T i) (T j))→(∀ i,((T i).card:ℝ)=a i*k)→
      (∀ C₀,R C₀⊆Finset.univ.biUnion T)→(∀ C₀ i,(R C₀∩T i).card=a i)→
      (∀ Y:Finset W,Fintype.card {C₀:C // R C₀=Y}≤J)→
      (∀ C₀,b/k^(c-1)≤w C₀ ∧ w C₀≤B/k^(c-1))→
      (∀ v∈Finset.univ.biUnion T,|1-hypergraphWeightedDegree R w v|≤η)→
      (∀ X:Finset W,X⊆Finset.univ.biUnion T→(∀ i,(X∩T i).card=a i)→
        α*k^(c*c)≤Fintype.card (LabelledAbsorberFamily R S X))→
      ∀ (I Z:Finset W) (z:ℕ),(I.card:ℝ)≤F₀→Z⊆Finset.univ.biUnion T→
      (∀ i,(Z∩T i).card=a i*z)→z≤q→
      ∀ E:Finset (W×W),(∀ p∈E,p.1≠p.2)→(E.card:ℝ)≤D*k→
      ∀ P:C→Finset (W×W),(∀ C₀,∀ p∈P C₀,p.1≠p.2∧p.1∈R C₀∧p.2∈R C₀)→
      (∀ C₀,(P C₀).card≤c)→(∀ C₀ v,((P C₀).filter (fun p=>v=p.1∨v=p.2)).card≤2)→
      ∃ A:Finset W,∃ D₀ D₁:Finset C,A⊆Finset.univ.biUnion T ∧ Disjoint A (Z∪I) ∧
        (∀ i,(A∩T i).card=a i*t) ∧
        (∀ p∈E,¬(p.1∈A∧p.2∈A)) ∧
        ((∀ x∈D₀,∀ y∈D₀,x≠y→Disjoint (R x) (R y)) ∧ D₀.biUnion R=A) ∧
        ((∀ x∈D₁,∀ y∈D₁,x≠y→Disjoint (R x) (R y)) ∧ D₁.biUnion R=A∪Z) ∧
        Disjoint (D₀.biUnion P) (D₁.biUnion P) ∧ ∀ C₀∈D₁,(R C₀∩Z).card≤1:=by
  obtain ⟨η,hη,hbase⟩:=supported_bounded_factors hs a c J hc hJ ha has S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ D hF₀ hD
  refine ⟨k₀,hk₀,?_⟩
  intro k hk W C _ _ _ _ T R w hTd hTc hsupp hR hmult hw herr habs I Z z hI hZT hZ hz E hE hEc P hP hPc hPd
  let V:Fin s→Type:=fun i=>T i
  let e:(Σ i,V i)↪W:=⟨fun v=>v.2.val,by
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    change x.val=y.val at h
    have hij:i=j:=by
      by_contra hn
      exact Finset.disjoint_left.mp (hTd i j hn) x.property (h.symm ▸ y.property)
    subst j
    exact congrArg (Sigma.mk i) (Subtype.ext h)⟩
  let ep:((Σ i,V i)×(Σ i,V i))↪(W×W):=
    ⟨fun p=>(e p.1,e p.2),by intro p q h;exact Prod.ext (e.injective (congrArg Prod.fst h)) (e.injective (congrArg Prod.snd h))⟩
  have hsupport (v:W) (hv:v∈Finset.univ.biUnion T):∃ x,e x=v:=by
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
    exact ⟨⟨i,⟨v,hi⟩⟩,rfl⟩
  have hclass (Y:Finset W) (i:Fin s):
      (Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈Y)).card=(Y∩T i).card:=by
    apply Finset.card_bij (fun v _=>v.val)
    · intro v hv;exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hv).2,v.property⟩
    · intro v _ w _ h;exact Subtype.ext h
    · intro v hv;exact ⟨⟨v,(Finset.mem_inter.mp hv).2⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_inter.mp hv).1⟩,rfl⟩
  have himageclass (Y:Finset (Σ i,V i)) (i:Fin s):
      (Y.image e∩T i).card=(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card:=by
    rw [←hclass]
    congr 1
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · rintro ⟨x,hx,he⟩;exact e.injective he ▸ hx
    · intro hv;exact ⟨⟨i,v⟩,hv,rfl⟩
  have hPimage (C₀:C):(embeddedPreimage ep (P C₀)).image ep=P C₀:=by
    apply embeddedPreimage_image
    intro p hp
    obtain ⟨x,hx⟩:=hsupport p.1 (hsupp C₀ (hP C₀ p hp).2.1)
    obtain ⟨y,hy⟩:=hsupport p.2 (hsupp C₀ (hP C₀ p hp).2.2)
    exact ⟨(x,y),Prod.ext hx hy⟩
  let I':=embeddedPreimage e I
  let Z':=embeddedPreimage e Z
  let E':=embeddedPreimage ep E
  let P':=fun C₀=>embeddedPreimage ep (P C₀)
  have hZimage:Z'.image e=Z:=embeddedPreimage_image e Z (fun v hv=>hsupport v (hZT hv))
  have hIbound:(I'.card:ℝ)≤F₀:=by
    apply le_trans _ hI
    exact_mod_cast (show I'.card≤I.card from Finset.card_le_card_of_injOn e
      (fun v hv=>(embeddedPreimage_mem e I v).mp hv) (fun _ _ _ _ h=>e.injective h))
  have hEbound:(E'.card:ℝ)≤D*k:=by
    apply le_trans _ hEc
    exact_mod_cast (show E'.card≤E.card from Finset.card_le_card_of_injOn ep
      (fun p hp=>(embeddedPreimage_mem ep E p).mp hp) (fun _ _ _ _ h=>ep.injective h))
  have hPcard (C₀:C):(P' C₀).card≤c:=by
    have hh:=congrArg Finset.card (hPimage C₀)
    rw [Finset.card_image_of_injective _ ep.injective] at hh
    exact hh.trans_le (hPc C₀)
  have hPdeg (C₀:C) (v:Σ i,V i):((P' C₀).filter (fun p=>v=p.1∨v=p.2)).card≤2:=by
    apply le_trans _ (hPd C₀ (e v))
    apply Finset.card_le_card_of_injOn ep
    · intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp,hvp⟩
      refine Finset.mem_filter.mpr ⟨(embeddedPreimage_mem ep (P C₀) p).mp hp,?_⟩
      exact hvp.elim (fun h=>Or.inl (congrArg e h)) (fun h=>Or.inr (congrArg e h))
    · intro _ _ _ _ h;exact ep.injective h
  obtain ⟨A,M₀,M₁,hAZ,hA,hAE,hM₀,hM₁,hdis,hcap⟩:=hbase k hk V W C e R w
    (fun i=>by simpa only [V,Fintype.card_coe] using hTc i)
    (fun C₀ v hv=>hsupport v (hsupp C₀ hv))
    (fun C₀ i=>(hclass (R C₀) i).trans (hR C₀ i)) hmult hw
    (fun v=>herr _ (Finset.mem_biUnion.mpr ⟨v.1,Finset.mem_univ _,v.2.property⟩)) (by
      intro σ
      apply habs
      · intro v hv;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
        exact Finset.mem_biUnion.mpr ⟨x.1,Finset.mem_univ _,x.2.property⟩
      · intro i;rw [himageclass];exact profileRootSet_class_card σ i)
    I' Z' z hIbound hz (fun i=>by
      simpa only [Z',embeddedPreimage_mem] using (hclass Z i).trans (hZ i))
    E' (fun p hp h=>hE (ep p) ((embeddedPreimage_mem ep E p).mp hp) (congrArg e h)) hEbound P'
    (fun C₀ p hp=>⟨fun he=>(hP C₀ (ep p) ((embeddedPreimage_mem ep (P C₀) p).mp hp)).1 (congrArg e he),
      (hP C₀ (ep p) ((embeddedPreimage_mem ep (P C₀) p).mp hp)).2⟩) hPcard hPdeg
  have hdisP:Disjoint (M₀.biUnion P) (M₁.biUnion P):=by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨C₀,hC₀,hp⟩:=Finset.mem_biUnion.mp hp
    obtain ⟨C₁,hC₁,hq⟩:=Finset.mem_biUnion.mp hq
    obtain ⟨p',hp',he⟩:=Finset.mem_image.mp ((hPimage C₀).symm ▸ hp)
    have hq':p'∈P' C₁:=(embeddedPreimage_mem ep (P C₁) p').mpr (he.symm ▸ hq)
    exact Finset.disjoint_left.mp hdis (Finset.mem_biUnion.mpr ⟨C₀,hC₀,hp'⟩)
      (Finset.mem_biUnion.mpr ⟨C₁,hC₁,hq'⟩)
  refine ⟨A.image e,M₀,M₁,?_,?_,fun i=>(himageclass A i).trans (hA i),?_,hM₀,?_,hdisP,?_⟩
  · intro v hv;obtain ⟨x,_,rfl⟩:=Finset.mem_image.mp hv
    exact Finset.mem_biUnion.mpr ⟨x.1,Finset.mem_univ _,x.2.property⟩
  · apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    apply Finset.disjoint_left.mp hAZ hx
    rcases Finset.mem_union.mp hv' with hz|hi
    · exact Finset.mem_union_left _ ((embeddedPreimage_mem e Z x).mpr hz)
    · exact Finset.mem_union_right _ ((embeddedPreimage_mem e I x).mpr hi)
  · intro p hp hpa
    obtain ⟨x,hx,hxv⟩:=Finset.mem_image.mp hpa.1
    obtain ⟨y,hy,hyv⟩:=Finset.mem_image.mp hpa.2
    have hep:ep (x,y)=p:=Prod.ext hxv hyv
    exact hAE (x,y) ((embeddedPreimage_mem ep E (x,y)).mpr (hep.symm ▸ hp)) ⟨hx,hy⟩
  · simpa only [Finset.image_union,hZimage] using hM₁
  · simpa only [hZimage] using hcap

end Oberwolfach
