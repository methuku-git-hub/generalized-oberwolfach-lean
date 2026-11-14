module

public import Oberwolfach.ProfileBoundedExtension
public import Oberwolfach.SupportedResourceFactors

@[expose] public section

/-! The bounded two-factor theorem on an embedded domain. The original
candidate identifiers and coefficients are retained, and the two returned
factors use the same chosen sample and the same displayed edge sets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 6500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {W Z C : Type} [Fintype W] [DecidableEq W] [Fintype Z] [DecidableEq Z]
  [Fintype C] [DecidableEq C]

theorem restricted_factor_lift_exact (R:C→Finset W) (e:Z↪W)
    (M:Finset (RestrictedResource R e)) (A:Finset Z)
    (hM:∀ x∈M,∀ y∈M,x≠y→Disjoint (restrictedResourceSet R e x) (restrictedResourceSet R e y))
    (hcover:M.biUnion (restrictedResourceSet R e)=A):
    (∀ x∈M.image Subtype.val,∀ y∈M.image Subtype.val,x≠y→Disjoint (R x) (R y)) ∧
      (M.image Subtype.val).biUnion R=A.image e:=by
  constructor
  · intro x hx y hy hne
    obtain ⟨x',hx',rfl⟩:=Finset.mem_image.mp hx
    obtain ⟨y',hy',rfl⟩:=Finset.mem_image.mp hy
    rw [←restrictedResourceSet_image R e x',←restrictedResourceSet_image R e y']
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨w,hw,he⟩:=Finset.mem_image.mp hb
    have he':w=v:=e.injective he
    subst w
    exact Finset.disjoint_left.mp (hM x' hx' y' hy' (fun h=>hne (congrArg Subtype.val h))) hv hw
  · rw [←hcover]
    ext a
    simp only [Finset.mem_biUnion,Finset.mem_image]
    constructor
    · rintro ⟨_,⟨D,hD,rfl⟩,ha⟩
      obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp ((restrictedResourceSet_image R e D).symm ▸ ha)
      exact ⟨v,⟨D,hD,hv⟩,rfl⟩
    · rintro ⟨v,⟨D,hD,hv⟩,rfl⟩
      exact ⟨D.val,⟨D,hD,rfl⟩,(restrictedResourceSet_mem R e D v).mp hv⟩

variable {s:ℕ} {Tpl:Type} [Fintype Tpl] [DecidableEq Tpl]

theorem supported_bounded_factors (hspos:1≤s) (a:Fin s→ℕ) (c J:ℕ)
    (hc:3≤c) (hJpos:1≤J) (ha:∀ i,1≤a i) (hs:∑ i,a i=c)
    (S:Tpl→VertexAbsorberTemplate c) (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0<B):
    ∃ η:ℝ,0<η ∧ ∀ q:ℕ,∃ t:ℕ,1≤t ∧ ∀ F₀ D:ℝ,0≤F₀→0≤D→
      ∃ k₀:ℝ,1<k₀ ∧ ∀ k:ℝ,k₀≤k→
        ∀ (V:Fin s→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
          (W C:Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
        ∀ (e:(Σ i,V i)↪W) (R:C→Finset W) (w:C→ℝ),
        (∀ i,(Fintype.card (V i):ℝ)=a i*k)→
        (∀ C₀,∀ v∈R C₀,∃ z,e z=v)→
        (∀ C₀ i,(Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈R C₀)).card=a i)→
        (∀ Y:Finset W,Fintype.card {C₀:C // R C₀=Y}≤J)→
        (∀ C₀,b/k^(c-1)≤w C₀ ∧ w C₀≤B/k^(c-1))→
        (∀ v,|1-hypergraphWeightedDegree R w (e v)|≤η)→
        (∀ σ:∀ i,FixedSubset (V i) (a i),α*k^(c*c)≤
          Fintype.card (LabelledAbsorberFamily R S ((profileRootSet σ).image e)))→
        ∀ (T Z:Finset (Σ i,V i)) (z:ℕ),(T.card:ℝ)≤F₀→z≤q→
        (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Z)).card=a i*z)→
        ∀ E:Finset ((Σ i,V i)×(Σ i,V i)),(∀ p∈E,p.1≠p.2)→(E.card:ℝ)≤D*k→
        ∀ P:C→Finset ((Σ i,V i)×(Σ i,V i)),
        (∀ C₀,∀ p∈P C₀,p.1≠p.2 ∧ e p.1∈R C₀ ∧ e p.2∈R C₀)→
        (∀ C₀,(P C₀).card≤c)→
        (∀ C₀ v,((P C₀).filter (fun p=>v=p.1∨v=p.2)).card≤2)→
        ∃ A:Finset (Σ i,V i),∃ D₀ D₁:Finset C,
          Disjoint A (Z∪T) ∧
          (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈A)).card=a i*t) ∧
          (∀ p∈E,¬(p.1∈A∧p.2∈A)) ∧
          ((∀ x∈D₀,∀ y∈D₀,x≠y→Disjoint (R x) (R y)) ∧ D₀.biUnion R=A.image e) ∧
          ((∀ x∈D₁,∀ y∈D₁,x≠y→Disjoint (R x) (R y)) ∧ D₁.biUnion R=(A∪Z).image e) ∧
          Disjoint (D₀.biUnion P) (D₁.biUnion P) ∧
          ∀ C₀∈D₁,(R C₀∩Z.image e).card≤1:=by
  obtain ⟨η,hη,hbase⟩:=profile_two_bounded_factors hspos a c J hc hJpos ha hs S α b B hα hb hB
  refine ⟨η,hη,?_⟩
  intro q
  obtain ⟨t,ht,hbase⟩:=hbase q
  refine ⟨t,ht,?_⟩
  intro F₀ D hF₀ hD
  obtain ⟨k₀,hk₀,hbase⟩:=hbase F₀ D hF₀ hD
  refine ⟨k₀,hk₀,?_⟩
  intro k hk V _ _ W C _ _ _ _ e R w hn hsupp hR hJ hw herr habs T Z z hT hz hZ E hE hEc P hP hPc hPd
  have hprofile (C₀:RestrictedResource R e) (i:Fin s):
      (Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈restrictedResourceSet R e C₀)).card=a i:=by
    simpa only [restrictedResourceSet_mem] using hR C₀.val i
  have hdegree (v:Σ i,V i):hypergraphWeightedDegree (restrictedResourceSet R e) (fun C₀=>w C₀.val) v=
      hypergraphWeightedDegree R w (e v):=by
    rw [restricted_resource_degree]
    congr 1
    funext C₀
    rw [if_pos (hsupp C₀)]
  obtain ⟨A,M₀,M₁,hAZ,hA,hAE,hM₀,hM₁,hdis,hcap⟩:=hbase k hk V (RestrictedResource R e)
    (restrictedResourceSet R e) (fun C₀=>w C₀.val) hn hprofile (restricted_resource_multiplicity R e J hJ)
    (fun C₀=>hw C₀.val) (fun v=>by rw [hdegree];exact herr v)
    (fun σ=>(habs σ).trans (by exact_mod_cast all_supported_absorber_family_card R e hsupp S (profileRootSet σ)))
    T Z z hT hz hZ E hE hEc (fun C₀=>P C₀.val)
    (fun C₀ p hp=>⟨(hP C₀.val p hp).1,
      (restrictedResourceSet_mem R e C₀ p.1).mpr (hP C₀.val p hp).2.1,
      (restrictedResourceSet_mem R e C₀ p.2).mpr (hP C₀.val p hp).2.2⟩)
    (fun C₀=>hPc C₀.val) (fun C₀=>hPd C₀.val)
  refine ⟨A,M₀.image Subtype.val,M₁.image Subtype.val,hAZ,hA,hAE,
    restricted_factor_lift_exact R e M₀ A hM₀.1 hM₀.2,
    restricted_factor_lift_exact R e M₁ (A∪Z) hM₁.1 hM₁.2,?_,?_⟩
  · have himage (M:Finset (RestrictedResource R e)):
        (M.image Subtype.val).biUnion P=M.biUnion (fun C₀=>P C₀.val):=by
      ext p
      simp only [Finset.mem_biUnion,Finset.mem_image]
      constructor
      · rintro ⟨_,⟨C₀,hC₀,rfl⟩,hp⟩;exact ⟨C₀,hC₀,hp⟩
      · rintro ⟨C₀,hC₀,hp⟩;exact ⟨C₀.val,⟨C₀,hC₀,rfl⟩,hp⟩
    rw [himage,himage]
    exact hdis
  · intro C₀ hC₀
    obtain ⟨C',hC',rfl⟩:=Finset.mem_image.mp hC₀
    have he:(R C'.val∩Z.image e)=(restrictedResourceSet R e C'∩Z).image e:=by
      rw [Finset.image_inter _ _ e.injective,restrictedResourceSet_image]
    rw [he,Finset.card_image_of_injective _ e.injective]
    exact hcap C' hC'

end Oberwolfach
