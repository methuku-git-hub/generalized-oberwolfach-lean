module

public import Oberwolfach.EndpointTriangleFactor
public import Oberwolfach.SupportedBernoulliFactor
public import Oberwolfach.EmbeddedFiniteSets

@[expose] public section

/-! Fresh endpoint triangle factors on the two original classes. No exact
ratio is imposed before sampling. The final ratio is imposed on the altered
classes, and the paired absorbers are constructed from the actual counts. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 512
set_option maxHeartbeats 8500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem endpoint_triangle_fresh_factor (γ b B:ℝ) (hγ:0<γ) (hb:0<b) (hB:0≤B):
    ∃ ε η ζ:ℝ,0<ε ∧ 0<η ∧ 0<ζ ∧ ∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,
      ∀ (A:Type) [Fintype A] [DecidableEq A],N≤Fintype.card A→
      ∀ (Q F:SimpleGraph A) (S T:Finset A),Disjoint S T→
      (∀ v,(F.degree v:ℝ)≤ε*Fintype.card A)→
      EndpointNeighbourCounts Q F S T (γ*Fintype.card A)→
      ∀ wt:EndpointTriangle Q F S T→ℝ,
      (∀ C,b/(Fintype.card A:ℝ)^2≤wt C ∧ wt C≤B/(Fintype.card A:ℝ)^2)→
      (∀ v∈S∪T,|1-hypergraphWeightedDegree endpointTriangleVertices wt v|≤η)→
      1-1/(T.card:ℝ)^q≤
        (FiniteLaw.pi (fun _:A=>FiniteLaw.retentionCoin p hp.le hp1)).probability
          (fun σ=>∀ Y:Finset A,Y⊆S∪T→(Y∩S).card=2*(Y∩T).card→
            (((((S∪T)∩bernoulliVertexSet σ)\Y).card+
              (Y\((S∪T)∩bernoulliVertexSet σ)).card:ℕ):ℝ)≤ζ*(p*T.card)→
            ∀ K:SimpleGraph A,(∀ v,(K.degree v:ℝ)≤ζ*(p*T.card))→
            ∃ D:Finset (EndpointTriangle Q F S T),
              ((∀ C∈D,∀ E∈D,C≠E→Disjoint (endpointTriangleVertices C) (endpointTriangleVertices E)) ∧
                D.biUnion endpointTriangleVertices=Y) ∧
              ∀ C∈D,∀ x∈endpointTriangleVertices C,∀ y∈endpointTriangleVertices C,¬K.Adj x y):=by
  let β:=ordinaryLocalCountCoeff 2 γ
  have hβ:0<β:=ordinaryLocalCountCoeff_pos 2 γ hγ
  let α:=(β/2)^4
  have hα:0<α:=by dsimp [α];positivity
  let Templates:Unit→VertexAbsorberTemplate 3:=fun _=>pairedAbsorberTemplate 3
  obtain ⟨η,ζ,hη,hζ,hfresh⟩:=supported_bernoulli_graph_avoiding_factor (twoClassProfile 2) 3 1
    (by norm_num) (by intro i;cases i <;> norm_num [twoClassProfile]) (twoClassProfile_sum 2)
    Templates α (b*γ^2) B hα (by positivity) hB
  let ε:=γ/24
  have hε:0<ε:=by dsimp [ε];positivity
  obtain ⟨Na,hNa⟩:=paired_absorber_order_threshold 2 β hβ
  refine ⟨ε,η,ζ,hε,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf⟩:=hfresh p hp hp1 q
  obtain ⟨N₁,hN₁⟩:=exists_nat_gt (max (24/γ) ((Nf:ℝ)/γ))
  refine ⟨max Na (max N₁ 1),?_⟩
  intro A _ _ hn Q F S T hST hF hcommon wt hw herr
  let n:ℝ:=Fintype.card A
  let H₀:A→Unit→Prop:=fun v _=>v∈S
  let H₁:A→Unit→Prop:=fun v _=>v∈T
  have hd (v:A):¬(H₀ v ()∧H₁ v ()):=fun h=>Finset.disjoint_left.mp hST h.1 h.2
  let V:=hubNeighbourClass H₀ H₁ ()
  let e:=hubNeighbourEmbedding H₀ H₁ () hd
  let C:=EndpointTriangle Q F S T
  let R:C→Finset A:=endpointTriangleVertices
  have heimage:Finset.univ.image e=S∪T:=by
    rw [hubNeighbourEmbedding_image];ext v;simp [H₀,H₁]
  have htotal:Fintype.card (Σ i,V i)=(S∪T).card:=by
    have hh:=congrArg Finset.card heimage
    simpa only [Finset.card_image_of_injective _ e.injective,Finset.card_univ] using hh
  have hnpos:0<n:=by dsimp [n];exact_mod_cast (show 0<Fintype.card A by omega)
  have hNn:(N₁:ℝ)≤n:=by dsimp [n];exact_mod_cast (show N₁≤Fintype.card A by omega)
  have hlarge:24≤γ*n:=by
    have hh:=(div_le_iff₀ hγ).mp ((le_max_left _ _).trans (hN₁.le.trans hNn))
    linarith only [hh]
  have hbudget:6*(ε*n+1)≤γ/2*n:=by dsimp [ε];nlinarith only [hlarge]
  have hsize:γ*n≤(T.card:ℝ):=hcommon.indices
  have hTpos:(0:ℝ)<T.card:=(mul_pos hγ hnpos).trans_le hsize
  have htU:(T.card:ℝ)≤(S∪T).card:=by exact_mod_cast Finset.card_le_card Finset.subset_union_right
  have hUpos:(0:ℝ)<(S∪T).card:=hTpos.trans_le htU
  have hUn:((S∪T).card:ℝ)≤n:=by dsimp [n];exact_mod_cast Finset.card_le_univ (S∪T)
  have hNU:Nf≤Fintype.card (Σ i,V i):=by
    rw [htotal]
    have hh:=(div_le_iff₀ hγ).mp ((le_max_right _ _).trans (hN₁.le.trans hNn))
    exact_mod_cast (show (Nf:ℝ)≤(S∪T).card from by linarith only [hh,hsize,htU])
  have hsupp (c:C) (v:A) (hv:v∈R c):∃ z,e z=v:=by
    have hh:=c.property.1 hv
    rw [←heimage] at hh
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using hh
  have hclass (X:Finset A) (i:Bool):
      (Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈X)).card=(X∩(if i then T else S)).card:=by
    apply Finset.card_bij (fun v _=>v.val)
    · intro v hv;exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hv).2,by cases i <;> exact v.property⟩
    · intro v _ w _ h;exact Subtype.ext h
    · intro v hv
      exact ⟨⟨v,by cases i <;> exact (Finset.mem_inter.mp hv).2⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_inter.mp hv).1⟩,rfl⟩
  have hprofile (c:C) (i:Bool):
      (Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈R c)).card=twoClassProfile 2 i:=by
    rw [hclass];cases i
    · exact c.property.2.1
    · exact c.property.2.2.1
  have hwt (c:C):(b*γ^2)/(Fintype.card (Σ i,V i):ℝ)^(3-1)≤wt c ∧
      wt c≤B/(Fintype.card (Σ i,V i):ℝ)^(3-1):=by
    rw [htotal]
    exact hub_factor_weight_scale 2 n (S∪T).card γ b B (wt c) hnpos hUpos hγ hb.le hB hUn (hsize.trans htU) (hw c)
  have hevent:=hNf V A C hNU e R wt hsupp hprofile (endpointTriangle_multiplicity Q F S T) hwt
    (fun v=>herr _ (by rw [←heimage];exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩)) (by
      intro ρ
      obtain ⟨x,hx,hxset,hxT,hxS⟩:=exists_twoClass_root_order ρ
      have hroot (i:Fin 3):e (x i)∈endpointBaseClass S T i.val:=by
        refine Fin.cases ?_ (fun j=>?_) i
        · have hh:=(embedded_class_image_iff e true (x 0)).mpr hxT
          obtain ⟨z,hz⟩:=hh;exact hz ▸ z.property
        · have hh:=(embedded_class_image_iff e false (x j.succ)).mpr (hxS j)
          obtain ⟨z,hz⟩:=hh;simpa [endpointBaseClass] using (hz ▸ z.property)
      have hcounts:=hNa (Fintype.card A) (by omega)
      have habs:=endpoint_paired_absorber_count Q F S T hST γ (ε*n) hγ (by positivity)
        hF hcommon hbudget (by norm_num at hcounts ⊢;exact hcounts.1)
        (by norm_num at hcounts ⊢;exact hcounts.2) (fun i=>e (x i)) (e.injective.comp hx) hroot
      have hrootset:Finset.univ.image (fun i=>e (x i))=(profileRootSet ρ).image e:=by
        rw [←hxset,Finset.image_image];rfl
      rw [hrootset] at habs
      have hscale:α*(Fintype.card (Σ i,V i):ℝ)^9≤α*n^9:=by
        rw [htotal];exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hUpos.le hUn _) hα.le
      let embed:LabelledCycleRecord R (pairedAbsorberTemplate 3).val ((profileRootSet ρ).image e)→
          LabelledAbsorberFamily R Templates ((profileRootSet ρ).image e):=fun D=>⟨(),D⟩
      have hi:Function.Injective embed:=by intro D E he;exact eq_of_heq (Sigma.mk.inj_iff.mp he).2
      exact (hscale.trans habs).trans (by exact_mod_cast Fintype.card_le_of_injective embed hi))
  rw [htotal] at hevent
  have hprob:1-1/(T.card:ℝ)^q≤1-1/((S∪T).card:ℝ)^q:=by
    exact sub_le_sub_left (div_le_div_of_nonneg_left (by norm_num) (pow_pos hTpos _) (pow_le_pow_left₀ hTpos.le htU _)) 1
  apply (hprob.trans hevent).trans
  apply finiteLaw_probability_mono
  intro σ hσ Y hYU hratio hchange K hK
  let Y':=embeddedPreimage e Y
  have hYsupp:∀ v∈Y,∃ z,e z=v:=by
    intro v hv;have hh:=hYU hv;rw [←heimage] at hh
    simpa only [Finset.mem_image,Finset.mem_univ,true_and] using hh
  have hYprofile (i:Bool):
      (Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y')).card=twoClassProfile 2 i*(Y∩T).card:=by
    have he:(Finset.univ.filter (fun v:V i=>(⟨i,v⟩:Σ i,V i)∈Y'))=
        Finset.univ.filter (fun v:V i=>e ⟨i,v⟩∈Y):=
      Finset.filter_congr (fun v _=>embeddedPreimage_mem e Y ⟨i,v⟩)
    rw [he,hclass]
    cases i
    · exact hratio
    · simp [twoClassProfile]
  have hscale:ζ*(p*T.card)≤ζ*(p*(S∪T).card):=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left htU hp.le) hζ.le
  have hdiff:(((bernoulliVertexSet (fun z=>σ (e z))\Y').card+
      (Y'\bernoulliVertexSet (fun z=>σ (e z))).card:ℕ):ℝ)≤ζ*(p*(S∪T).card):=by
    rw [embedded_bernoulli_alteration e σ Y hYsupp,heimage]
    exact hchange.trans hscale
  obtain ⟨D,hD,havoid⟩:=hσ Y' (Y∩T).card hYprofile hdiff K (fun v=>(hK v).trans hscale)
  exact ⟨D,⟨hD.1,hD.2.trans (embeddedPreimage_image e Y hYsupp)⟩,havoid⟩

end Oberwolfach
