module

public import Oberwolfach.BernoulliGraphAvoidingFactor
public import Oberwolfach.SupportedResourceFactors
public import Oberwolfach.FiniteProductProjection

@[expose] public section

/-! The fresh factor theorem on fixed embedded physical domains. Resource
identifiers, parent weights and the independent-coordinate law are preserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256
set_option maxHeartbeats 8500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {W Z C:Type} [Fintype W] [DecidableEq W] [Fintype Z] [DecidableEq Z]
    [Fintype C] [DecidableEq C]

theorem graph_comap_degree_le (F:SimpleGraph W) (e:Z↪W) (v:Z):
    (F.comap e).degree v≤F.degree (e v):=by
  have hs:((F.comap e).neighborFinset v).image e⊆F.neighborFinset (e v):=by
    intro w hw
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hw
    have hh:=(SimpleGraph.mem_neighborFinset _ _ _).mp hz
    exact (SimpleGraph.mem_neighborFinset _ _ _).mpr hh
  have hh:=Finset.card_le_card hs
  simpa only [Finset.card_image_of_injective _ e.injective,
    SimpleGraph.card_neighborFinset_eq_degree] using hh

theorem restricted_decomposition_with_predicate_lift (R:C→Finset W) (e:Z↪W)
    (Y:Finset Z) (P:C→Prop)
    (h:∃ D:Finset (RestrictedResource R e),
      ((∀ x∈D,∀ y∈D,x≠y→Disjoint (restrictedResourceSet R e x) (restrictedResourceSet R e y)) ∧
        D.biUnion (restrictedResourceSet R e)=Y) ∧ ∀ x∈D,P x.val):
    ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧
      D.biUnion R=Y.image e) ∧ ∀ x∈D,P x:=by
  obtain ⟨D,⟨hd,hu⟩,hp⟩:=h
  refine ⟨D.image Subtype.val,⟨?_,?_⟩,?_⟩
  · intro a ha b hb hab
    obtain ⟨a',ha',rfl⟩:=Finset.mem_image.mp ha
    obtain ⟨b',hb',rfl⟩:=Finset.mem_image.mp hb
    rw [←restrictedResourceSet_image R e a',←restrictedResourceSet_image R e b']
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
    obtain ⟨y,hy,he⟩:=Finset.mem_image.mp hw
    have he':=e.injective he
    subst y
    exact Finset.disjoint_left.mp (hd a' ha' b' hb' (fun h=>hab (congrArg Subtype.val h))) hx hy
  · rw [←hu]
    ext v
    constructor
    · intro hv
      obtain ⟨C₀,hC,hv⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨D₀,hD,rfl⟩:=Finset.mem_image.mp hC
      rw [←restrictedResourceSet_image R e D₀] at hv
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨x,Finset.mem_biUnion.mpr ⟨D₀,hD,hx⟩,rfl⟩
    · intro hv
      obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hv
      obtain ⟨D₀,hD,hx⟩:=Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨D₀.val,Finset.mem_image.mpr ⟨D₀,hD,rfl⟩,
        (restrictedResourceSet_mem R e D₀ x).mp hx⟩
  · intro x hx
    obtain ⟨x',hx',rfl⟩:=Finset.mem_image.mp hx
    exact hp x' hx'

variable {I T:Type} [Fintype I] [DecidableEq I] [Nonempty I] [Fintype T] [DecidableEq T]

theorem supported_bernoulli_graph_avoiding_factor (a:I→ℕ) (c J:ℕ) (hc:3≤c)
    (ha:∀ i,1≤a i) (hs:∑ i,a i=c) (S:T→VertexAbsorberTemplate c)
    (α b B:ℝ) (hα:0<α) (hb:0<b) (hB:0≤B):
    ∃ η ζ:ℝ,0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (V:I→Type) [∀ i,Fintype (V i)] [∀ i,DecidableEq (V i)]
        (W C:Type) [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C],
      N≤Fintype.card (Σ i,V i)→∀ (e:(Σ i,V i)↪W) (R:C→Finset W) (w:C→ℝ),
      (∀ C₀,∀ v∈R C₀,∃ z,e z=v)→
      (∀ C₀ i,(Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈R C₀)).card=a i)→
      (∀ U:Finset W,Fintype.card {C₀:C // R C₀=U}≤J)→
      (∀ C₀,b/(Fintype.card (Σ i,V i):ℝ)^(c-1)≤w C₀ ∧
        w C₀≤B/(Fintype.card (Σ i,V i):ℝ)^(c-1))→
      (∀ v,|1-hypergraphWeightedDegree R w (e v)|≤η)→
      (∀ ρ:∀ i,FixedSubset (V i) (a i),
        α*(Fintype.card (Σ i,V i):ℝ)^(c*c)≤
          Fintype.card (LabelledAbsorberFamily R S ((profileRootSet ρ).image e)))→
      1-1/(Fintype.card (Σ i,V i):ℝ)^q≤
        (FiniteLaw.pi (fun _:W=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ (Y:Finset (Σ i,V i)) (k:ℕ),
            (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=a i*k)→
            (((bernoulliVertexSet (fun z=>σ (e z))\Y).card+
              (Y\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤ζ*(p*Fintype.card (Σ i,V i))→
            ∀ F:SimpleGraph W,(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
            ∃ D:Finset C,((∀ x∈D,∀ y∈D,x≠y→Disjoint (R x) (R y)) ∧ D.biUnion R=Y.image e) ∧
              ∀ C₀∈D,∀ x∈R C₀,∀ y∈R C₀,¬F.Adj x y):=by
  obtain ⟨η,ζ,hη,hζ,hbase⟩:=bernoulli_graph_avoiding_factor a c J hc ha hs S α b B hα hb hB
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨N,hN⟩:=hbase p hp hp1 q
  refine ⟨N,?_⟩
  intro V _ _ W C _ _ _ _ hn e R w hsupp hR hJ hw herr habs
  have hprofile (C₀:RestrictedResource R e) (i:I):
      (Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈restrictedResourceSet R e C₀)).card=a i:=by
    simpa only [restrictedResourceSet_mem] using hR C₀.val i
  have hdegree (v:Σ i,V i):hypergraphWeightedDegree (restrictedResourceSet R e) (fun C₀=>w C₀.val) v=
      hypergraphWeightedDegree R w (e v):=by
    rw [restricted_resource_degree]
    have he:(fun C₀=>if ∀ x∈R C₀,∃ z,e z=x then w C₀ else 0)=w:=by
      funext C₀;rw [if_pos (hsupp C₀)]
    rw [he]
  have hevent:=hN V (RestrictedResource R e) hn (restrictedResourceSet R e) (fun C₀=>w C₀.val)
    hprofile (restricted_resource_multiplicity R e J hJ) (fun C₀=>hw C₀.val)
    (fun v=>by rw [hdegree];exact herr v)
    (fun ρ=>(habs ρ).trans (by exact_mod_cast all_supported_absorber_family_card R e hsupp S (profileRootSet ρ)))
  let good:((Σ i,V i)→Bool)→Prop:=fun σ=>∀ (Y:Finset (Σ i,V i)) (k:ℕ),
    (∀ i,(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y)).card=a i*k)→
    (((bernoulliVertexSet σ\Y).card+(Y\bernoulliVertexSet σ).card:ℕ):ℝ)≤ζ*(p*Fintype.card (Σ i,V i))→
    ∀ F:SimpleGraph (Σ i,V i),(∀ v,(F.degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)))→
    ∃ D:Finset (RestrictedResource R e),
      ((∀ x∈D,∀ y∈D,x≠y→Disjoint (restrictedResourceSet R e x) (restrictedResourceSet R e y)) ∧
        D.biUnion (restrictedResourceSet R e)=Y) ∧
      ∀ C₀∈D,∀ x∈restrictedResourceSet R e C₀,∀ y∈restrictedResourceSet R e C₀,¬F.Adj x y
  have hprojection:=finiteLaw_pi_injective_projection_event
    (fun _:W=>FiniteLaw.retentionCoin p hp.le hp1) e e.injective good
  rw [←hprojection] at hevent
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σ hσ Y k hY hchange F hF
  have hdeg (v:Σ i,V i):((F.comap e).degree v:ℝ)≤ζ*(p*Fintype.card (Σ i,V i)):=
    (Nat.cast_le.mpr (graph_comap_degree_le F e v)).trans (hF (e v))
  obtain ⟨D,hD,havoid⟩:=hσ Y k hY hchange (F.comap e) hdeg
  apply restricted_decomposition_with_predicate_lift R e Y
    (fun C₀=>∀ x∈R C₀,∀ y∈R C₀,¬F.Adj x y)
  refine ⟨D,hD,?_⟩
  intro C₀ hC x hx y hy hxy
  obtain ⟨x',rfl⟩:=C₀.property x hx
  obtain ⟨y',rfl⟩:=C₀.property y hy
  have hx':x'∈restrictedResourceSet R e C₀:=(restrictedResourceSet_mem R e C₀ _).mpr hx
  have hy':y'∈restrictedResourceSet R e C₀:=(restrictedResourceSet_mem R e C₀ _).mpr hy
  exact havoid C₀ hC x' hx' y' hy' hxy

end Oberwolfach
