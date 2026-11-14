module

public import Oberwolfach.MarkedSampleActualBoundaryCompletionLocal
public import Oberwolfach.MarkedSampleActualBoundarySelectionUniform

@[expose] public section
/-! Completion of the actual boundary on the same sample, with numerical
choices fixed before the actual spoke density. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_actual_boundary_completion_local_uniform (r:ℕ) (hr:1≤r) (ν:ℝ) (hν:0<ν) (β aLo B pstar t₀ p₀ a gap omega:ℝ)
    (hβ:0<β) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar) (ht₀:0<t₀)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hgap:0<gap) (homega:0<omega) (homega1:omega≤1):
    ∃ η ηEnd ζ pmax:ℝ,0<η∧0<ηEnd∧0<ζ∧0<pmax∧pmax≤1/8∧∀ (d:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1),p≤pmax→∀ q:ℕ,∃ N:ℕ,1≤N∧
    ∀ t:ℝ,t₀≤t → ∀ (W V U Gamma Color J I:Type) [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V]
      [Fintype U] [DecidableEq U] [Fintype Gamma] [Fintype Color]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
    N≤Fintype.card W→ omega*Fintype.card (V⊕U)≤(Fintype.card W:ℝ)→Fintype.card J≤(Fintype.card W)^2→
    ∀ (f:W↪oV) (ρ:Equiv.Perm W) (π:Equiv.Perm V),(∀ x,f (ρ x)=π (f x))→
    ∀ (P:SimpleGraph V) (D τweight pr kr sr:ℝ),
    (Fintype.card W:ℝ)/2≤D→D≤2*Fintype.card W→
    pstar≤pr→pstar≤kr→pstar≤sr→pr≤1→kr≤1→sr≤1→
    ∀ weight:(Fin (r+4+1)→W)→ℝ,SuccessorSequenceWeightConditions (P.comap f) ρ (3*d) D τweight aLo B weight→
    ∀ (σ:RawMarkedOutcome V U Gamma Color) (H:Bool→V→U→Prop) (u:J↪U) (root:I↪V) (Zinner:Finset U),
    (∀ j,u j∉Zinner)→(∀ i,root i∉Finset.univ.image f)→
    (∀ u v,¬(H false v u∧H true v u))→
    (∀ u v z,H false v u→H true z u→v≠π z)→
    ∀ (Q:U→Gamma→ℝ) (S:U→Color→ℝ) (g:Gamma) (c:Color),
    (∀ u,Q u g=t)→
    MarkedRowsWithSpokes (P.comap f) ρ d 1 Finset.univ pr kr Q S g c ((t/2)*Fintype.card W)
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→
    MarkedLocalConfigurationsWithSpokes r (P.comap f) ρ d Finset.univ β β
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→
    MarkedLocalSpokeLoadsWithSpokes (P.comap f) ρ d (r+4) D pr kr sr weight η
      (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u)→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2
    let X:=Finset.univ.image f;
    ∀ h:ℕ,3≤h→∀ errR errI:ℝ,0≤errR→0≤errI→
      2*errR≤ηEnd*(a*Fintype.card (V⊕U))→2*errI≤ηEnd*(a*Fintype.card (V⊕U))→
    MarkedRowsWithSpokes P π d h X pr kr Q S g c errR σ H→
    MarkedIndicesWithSpokes π d h Zinner Q S g c errI σ H→
    ∀ w:Bool→ℝ,(∀ u∈Zinner,Q u g=w true)→(∀ u∈Zinner,S u c=w false)→
      (∀ e,p₀≤w e∧w e≤1)→
    let L:=fun (j:I×Fin 5)=>markedEndpointLabels P π d X
      (markedEndpointFiveRimType j.2,markedEndpointFiveIncoming j.2,root j.1) σ
    let T:=fun (j:I×Fin 5)=>Zinner.filter (H (markedEndpointFiveRootSpokeType j.2) (root j.1));
      (∀ j,a*Fintype.card (V⊕U)≤((L j).card:ℝ)∧a*Fintype.card (V⊕U)≤((T j).card:ℝ))→
      (∀ i,((markedEndpointLabels P π d X (true,false,root i) σ).card:ℝ)+
        gap*Fintype.card (V⊕U)≤(Zinner.filter (H false (root i))).card)→
      (∀ v∉X,∃ i,root i=v)→(∀ v∉Zinner,∃ j,u j=v)→
      MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) X (β*Fintype.card (V⊕U))→
      1≤d→
      1-1/(Fintype.card W:ℝ)^q-3/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σb=>∀ M₀ M₁:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
          (∀ W∈M₀,∀ W'∈M₀,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
          (∀ W∈M₁,∀ W'∈M₁,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
          Disjoint (M₀.biUnion markedWheelPhysicalResources) (M₁.biUnion markedWheelPhysicalResources)→
          (∀ e∈M₀.biUnion markedWheelPhysicalResources,¬markedInnerResource X Zinner e)→
          (∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
            Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M₀.biUnion markedWheelPhysicalResources∪M₁.biUnion markedWheelPhysicalResources)→
          (∀ x u,x∉X→u∉Zinner→H false x u∨H true x u→Sum.inr (x,u)∈M₀.biUnion markedWheelPhysicalResources∪M₁.biUnion markedWheelPhysicalResources)→
          MarkedOutsideBalance tail head ktail khead (H true) Finset.univ
            (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)) (r+4) X Zinner→
          let G:=ordinaryBoundaryGraph (markedSampleArcSetGraph P π d σ Finset.univ)
            (fun x u=>H false x u∨H true x u) X Zinner
          let C:=ordinaryPhysicalGraph (markedPackingRimGraph M₀) (markedPackingSpokes M₀)
          let D₁:=ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁);
          Disjoint C (retainedGraph G σb)→
          (∀ x,(((G\retainedGraph G σb)\C).degree x:ℝ)≤p^9*Fintype.card (V⊕U))→
          (∀ x,(D₁.degree x:ℝ)≤p^3*Fintype.card (V⊕U))→
    ∃ N:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
      Disjoint ((M₀∪M₁).biUnion markedWheelPhysicalResources) (N.biUnion markedWheelPhysicalResources)∧
      (let M:=M₀∪M₁∪N
       (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))∧
       (∀ v,((spanningRestriction (markedPackingRimGraph M) X).degree v:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ v∈X,((Zinner.filter (markedPackingSpokes M v)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (∀ u∈Zinner,((X.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤ν*Fintype.card (V⊕U))∧
       (let A':=Finset.univ\M.biUnion markedWheelArcs
        let S':=(Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2))\M.biUnion markedWheelSpokePairs
        (∀ a∈A',Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)∧
          (∀ s∈S',s.1∈X∧s.2∈Zinner)∧
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)=
            (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
              (Finset.univ.filter (fun s:V×U=>H false s.1 s.2∨H true s.1 s.2)).image Sum.inr)\
              M.biUnion markedWheelPhysicalResources))):=by
  obtain ⟨η,ηEnd,ζ,pS,hη,hηEnd,hζ,hpS,hpS8,hsel⟩:=
    marked_sample_actual_boundary_selection_local_uniform r β aLo B pstar t₀ p₀ a gap omega
      hβ haLo hB hpstar ht₀ hp₀ hp₀1 ha ha1 hgap homega homega1
  obtain ⟨pF,hpF,hpF1,hfinish⟩:=marked_actual_boundary_finish_support r hr β ν hβ hν
  refine ⟨η,ηEnd,ζ,min pS pF,hη,hηEnd,hζ,lt_min hpS hpF,
    (min_le_left _ _).trans hpS8,?_⟩
  intro d p hp hp1 hpp q
  obtain ⟨NS,hNS1,hNS⟩:=hsel d p hp hp1 (hpp.trans (min_le_left _ _)) q
  by_cases hd:1≤d
  · obtain ⟨NF,hNF⟩:=hfinish p hp (hpp.trans (min_le_right _ _)) d hd
    refine ⟨max NS NF,by omega,?_⟩
    intro t ht W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hWlo hJ f ρ π hf P D τweight pr kr sr
      hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
      Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
      h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L T hsize hgapParent
      hroots hhubs Qext _
    have hWV:Fintype.card W≤Fintype.card V:=Fintype.card_le_of_injective f f.injective
    have hWn:Fintype.card W≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
    have hevent:=hNS t ht W V U Gamma Color J I (by omega) hWlo hJ f ρ π hf P D τweight pr kr sr
      hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
      Q S g c hQ hrows hconfigs hload h hh errR errI heR heI heRsmall heIsmall
      hrowEnd hidxEnd w hQw hSw hwprob hsize hgapParent
    apply hevent.trans
    apply finiteLaw_probability_mono
    intro σb hσ M₀ M₁ hM₀ hM₁ hM₀₁ hinner hArcs hSpokes hdiv G C D₁ hCR hleft hcover
    have hselected:=hσ M₀ M₁ hM₀ hM₁ hM₀₁ hArcs hSpokes hdiv hCR hleft hcover
    let DS:=ordinaryPhysicalGraph (markedPackingRimGraph (M₀∪M₁)) (markedPackingSpokes (M₀∪M₁))
    have hphys:ordinaryPhysicalGraph (markedPackingRimGraph M₀) (markedPackingSpokes M₀)⊔
        ordinaryPhysicalGraph (markedPackingRimGraph M₁) (markedPackingSpokes M₁)=DS:=
      (markedPackingPhysicalGraph_union M₀ M₁).symm
    have hrim:markedPackingRimGraph M₀⊔markedPackingRimGraph M₁=markedPackingRimGraph (M₀∪M₁):=
      (markedPackingRimGraph_union M₀ M₁).symm
    obtain ⟨F,Q',hcross,havoid,hdegree⟩:=hselected
    have hRclass (mark incoming:Bool) (i:I):
        markedEndpointLabels P π d X (mark,incoming,root i)
          (rawMarkedDeleteRims σ₀ (markedPackingRimGraph M₀⊔markedPackingRimGraph M₁).edgeFinset)=
        markedEndpointLabels P π d X (mark,incoming,root i)
          (rawMarkedDeleteRims σ₀ (markedPackingRimGraph (M₀∪M₁)).edgeFinset):=by
      have he:(markedPackingRimGraph M₀⊔markedPackingRimGraph M₁).edgeFinset=(markedPackingRimGraph (M₀∪M₁)).edgeFinset:=by
        ext e
        simp only [SimpleGraph.mem_edgeFinset,hrim]
      exact congrArg (fun D:Finset (Sym2 V)=>markedEndpointLabels P π d X (mark,incoming,root i) (rawMarkedDeleteRims σ₀ D)) he
    have hHclass (mark:Bool) (i:I):
        Zinner.filter (markedDeletePhysicalSpokes H (C⊔D₁) mark (root i))=
        Zinner.filter (markedDeletePhysicalSpokes H DS mark (root i)):=by
      congr 1
      congr 2
    have hY (j:J):
        (Finset.univ.filter (fun v:W=>(H false (f v) (u j)∨H true (f v) (u j))∧¬(C⊔D₁).Adj (Sum.inl (f v)) (Sum.inr (u j)))).image f=
        X.filter (fun x=>(H false x (u j)∨H true x (u j))∧¬DS.Adj (Sum.inl x) (Sum.inr (u j))):=by
      have he:=embedded_filtered_class_image f.toEmbedding
        (fun x=>(H false x (u j)∨H true x (u j))∧¬DS.Adj (Sum.inl x) (Sum.inr (u j)))
      convert he using 1 <;> congr!
    let F':=fun j=>(F j).changeSet (hY j)
    let Q'':=fun i=>(Q' i).changeSets (hRclass false true i) (hRclass true true i)
      (hRclass false false i) (hRclass true false i) (hHclass false i) (hHclass true i)
    have hFg (j:J):(F' j).graph=(F j).graph:=MarkedHubFactorOn.changeSet_graph _ _
    have hQg (i:I):(Q'' i).graph=(Q' i).graph:=MarkedEndpointPairing.changeSets_graph _ _ _ _ _ _ _
    have hgraphs:(fun x:J⊕I=>Sum.elim (fun j=>(F' j).graph) (fun i=>(Q'' i).graph) x)=
        (fun x:J⊕I=>Sum.elim (fun j=>(F j).graph) (fun i=>(Q' i).graph) x):=by
      funext x
      cases x <;> simp only [Sum.elim_inl,Sum.elim_inr,hFg,hQg]
    have hX:∀ x,π x∈X↔x∈X:=permutation_invariant_image f π ρ hf Finset.univ (by simp)
    refine hNF V U Gamma Color I J (by omega) P π σ₀ H X Zinner hX (fun x u=>hdtypes u x) hsep
      Qext root u hroot hu hroots hhubs M₀ M₁ hM₀ hM₁ hM₀₁ hinner
      (by simpa only [Finset.union_biUnion] using hArcs)
      (by simpa only [Finset.union_biUnion] using hSpokes) hcover F' Q'' ?_ ?_ ?_
    · intro i j hij
      simpa only [hgraphs] using hcross i j hij
    · intro i
      simpa only [hgraphs] using havoid i
    · intro z
      have hgSup:(⨆ i:J⊕I,Sum.elim (fun j=>(F' j).graph) (fun i=>(Q'' i).graph) i)=
          (⨆ i:J⊕I,Sum.elim (fun j=>(F j).graph) (fun i=>(Q' i).graph) i):=
        congrArg (fun g:J⊕I→SimpleGraph (V⊕U)=>⨆ i,g i) hgraphs
      simp only [←SimpleGraph.ncard_neighborSet,hgSup]
      simpa only [←SimpleGraph.ncard_neighborSet] using hdegree z
  · refine ⟨NS,hNS1,?_⟩
    intro t ht W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hWlo hJ f ρ π hf P D τweight pr kr sr
      hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hdtypes hsep
      Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
      h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L T hsize hgapParent
      hroots hhubs Qext hd'
    exact (hd hd').elim
end Oberwolfach
