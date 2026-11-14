module

public import Oberwolfach.MarkedSampleActualBoundarySelectionLocal
public import Oberwolfach.MarkedSampleRobustBoundarySelectionUniform

@[expose] public section
/-! The actual boundary selection is uniform over later spoke densities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_actual_boundary_selection_local_uniform (r:ℕ) (β aLo B pstar t₀ p₀ a gap omega:ℝ)
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
      1-1/(Fintype.card W:ℝ)^q-3/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σb=>∀ M₀ M₁:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
          (∀ W∈M₀,∀ W'∈M₀,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
          (∀ W∈M₁,∀ W'∈M₁,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
          Disjoint (M₀.biUnion markedWheelPhysicalResources) (M₁.biUnion markedWheelPhysicalResources)→
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
          let σ':=rawMarkedDeleteRims σ (markedPackingRimGraph M₀⊔markedPackingRimGraph M₁).edgeFinset
          let H':=markedDeletePhysicalSpokes H (C⊔D₁)
          let Y:=fun j:J=>Finset.univ.filter (fun v:W=>(H false (f v) (u j)∨H true (f v) (u j))∧¬(C⊔D₁).Adj (Sum.inl (f v)) (Sum.inr (u j)))
          let A₀:=fun i:I=>markedEndpointLabels P π d X (false,true,root i) σ'
          let A₁:=fun i:I=>markedEndpointLabels P π d X (true,true,root i) σ'
          let X₀:=fun i:I=>markedEndpointLabels P π d X (false,false,root i) σ'
          let X₁:=fun i:I=>markedEndpointLabels P π d X (true,false,root i) σ'
          let Y₀:=fun i:I=>Zinner.filter (H' false (root i))
          let Y₁:=fun i:I=>Zinner.filter (H' true (root i));
          ∃ F:∀ j,MarkedHubFactorOn tail head ktail khead (r+4) π (3*d) (H false) (H true) (u j) ((Y j).image f),
          ∃ Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) (H false) (H true) π (3*d),
          let K:J⊕I→SimpleGraph (V⊕U):=Sum.elim (fun j=>(F j).graph) (fun i=>(Q i).graph);
          (∀ i j,i≠j→Disjoint (K i) (K j))∧(∀ i,Disjoint (K i) D₁)∧
          ∀ z,((⨆ i,K i).degree z:ℝ)≤56*p*Fintype.card (V⊕U)):=by
  obtain ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,hsel⟩:=
    marked_sample_robust_boundary_selection_uniform r β aLo B pstar t₀ p₀ a gap omega
      hβ haLo hB hpstar ht₀ hp₀ hp₀1 ha ha1 hgap homega homega1
  refine ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,?_⟩
  intro d p hp hp1 hpp q
  obtain ⟨N,hN1,hN⟩:=hsel d p hp hp1 hpp q
  refine ⟨N,hN1,?_⟩
  intro t ht W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
    h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L T hsize hgapParent
  have hevent:=hN t ht W V U Gamma Color J I hn hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload h hh errR errI heR heI heRsmall heIsmall
    hrowEnd hidxEnd w hQw hSw hwprob hsize hgapParent
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σb hσ M₀ M₁ hM₀ hM₁ hM₀₁ hArcs hSpokes hdiv G C D₁ hCR hleft hcover
    σ' H' Y A₀ A₁ X₀ X₁ Y₀ Y₁
  have hX:∀ x,π x∈X↔x∈X:=permutation_invariant_image f π ρ hf Finset.univ (by simp)
  let τ:=fun e:Sym2 (V⊕U)=>decide (e∈((G\C)\D₁).edgeSet)
  have hmask:=marked_boundary_mask_after_packing tail head ktail khead π (H false) (H true)
    (markedSampleArc_physical_injective P π (3*d) _) X Zinner G C D₁ σb
    (marked_sample_boundary_physical_coin_mem P π d σ₀ H X Zinner hX)
    hCR (p^9*Fintype.card (V⊕U)) (p^3*Fintype.card (V⊕U)) hleft hcover
  have hchange:=marked_actual_boundary_class_changes P π d σ₀ H X Zinner hX
    (markedPackingRimGraph M₀) (markedPackingRimGraph M₁) (markedPackingSpokes M₀) (markedPackingSpokes M₁)
    σb (p^9*Fintype.card (V⊕U)) (p^3*Fintype.card (V⊕U)) hCR hleft hcover
  have hbalances:=marked_union_packing_boundary_balances_local P π d (r+4) σ₀ H
    (fun x u=>hd u x) X Zinner M₀ M₁ hM₀ hM₁ hM₀₁ hArcs hSpokes hdiv
  have hsupp:=marked_actual_boundary_support P π d σ₀ H X Zinner hX
    (markedPackingRimGraph M₀) (markedPackingRimGraph M₁) (markedPackingSpokes M₀) (markedPackingSpokes M₁)
  have hYratio (j:J):((Y j).filter (fun v=>H false (f v) (u j))).card=
      (r+4)*((Y j).filter (fun v=>H true (f v) (u j))).card:=by
    have he (b:Bool):((Y j).filter (fun v=>H b (f v) (u j))).card=
        ((X.filter (fun x=>(H false x (u j)∨H true x (u j))∧¬(C⊔D₁).Adj (Sum.inl x) (Sum.inr (u j)))).filter
          (fun x=>H b x (u j))).card:=by
      convert embedded_filtered_class_card f.toEmbedding
        (fun x=>(H false x (u j)∨H true x (u j))∧¬(C⊔D₁).Adj (Sum.inl x) (Sum.inr (u j)))
        (fun x=>H b x (u j)) using 1 <;> congr!
    rw [he false,he true]
    exact hbalances.2 (u j) (hu j)
  have hYchange (j:J):((changed (Y j)
      ((Finset.univ.filter (fun v=>H false (f v) (u j)∨H true (f v) (u j))).filter
        (fun v=>σb s(Sum.inl (f v),Sum.inr (u j))=true))).card:ℝ)≤(p^9+p^3)*Fintype.card (V⊕U):=by
    have he:=embedded_filtered_class_change_card f.toEmbedding
      (fun x=>(H false x (u j)∨H true x (u j))∧¬(C⊔D₁).Adj (Sum.inl x) (Sum.inr (u j)))
      (fun x=>(H false x (u j)∨H true x (u j))∧σb s(Sum.inl x,Sum.inr (u j))=true)
    have hh:=hchange.2.2 (u j) (hu j)
    have he':(changed (Y j)
        ((Finset.univ.filter (fun v=>H false (f v) (u j)∨H true (f v) (u j))).filter
          (fun v=>σb s(Sum.inl (f v),Sum.inr (u j))=true))).card=
        (changed (X.filter (fun x=>(H false x (u j)∨H true x (u j))∧¬(C⊔D₁).Adj (Sum.inl x) (Sum.inr (u j))))
          ((X.filter (fun x=>H false x (u j)∨H true x (u j))).filter
            (fun x=>σb s(Sum.inl x,Sum.inr (u j))=true))).card:=by
      convert he using 1 <;> try simp only [Y,Finset.filter_filter]
      all_goals congr!
    rw [he']
    convert hh using 1 <;> try ring
    all_goals congr!
  have hrowsFive (i:I) (j:Fin 5):markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j=
      markedEndpointLabels P π d X (markedEndpointFiveRimType j,markedEndpointFiveIncoming j,root i) σ':=by
    fin_cases j <;> rfl
  have hhubsFive (i:I) (j:Fin 5):markedEndpointFiveHubs (Y₀ i) (Y₁ i) j=
      Zinner.filter (H' (markedEndpointFiveRootSpokeType j) (root i)):=by
    fin_cases j <;> rfl
  obtain ⟨F,Q',hcross,havoid,hdegree⟩:=hσ τ
    (fun x=>by convert hmask x using 1 <;> ring)
    Y (fun j v hv=>(Finset.mem_filter.mp hv).2.1) hYratio hYchange A₀ A₁ X₀ X₁ Y₀ Y₁
    (fun i=>(hbalances.1 (root i) (hroot i)).1)
    (fun i=>(hbalances.1 (root i) (hroot i)).2.1)
    (fun i=>(hbalances.1 (root i) (hroot i)).2.2.1)
    (fun i=>(hbalances.1 (root i) (hroot i)).2.2.2) D₁ hcover
    (fun i j=>by rw [hrowsFive];exact marked_deleted_endpoint_subset P π d σ₀ X _ _ _ _)
    (fun i j=>by rw [hhubsFive];intro v hv;exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,(Finset.mem_filter.mp hv).2.1⟩)
    (fun i j=>by rw [hrowsFive];convert hchange.1 (markedEndpointFiveRimType j) (markedEndpointFiveIncoming j) (root i) (hroot i) using 1 <;> ring)
    (fun i j=>by rw [hhubsFive];convert hchange.2.1 (markedEndpointFiveRootSpokeType j) (root i) (hroot i) using 1 <;> ring)
    (fun j=>by
      have he:(Y j).image f=X.filter (fun x=>(H false x (u j)∨H true x (u j))∧¬(C⊔D₁).Adj (Sum.inl x) (Sum.inr (u j))):=by
        convert embedded_filtered_class_image f.toEmbedding
          (fun x=>(H false x (u j)∨H true x (u j))∧¬(C⊔D₁).Adj (Sum.inl x) (Sum.inr (u j))) using 1 <;> congr!
      rw [he]
      exact le_of_eq (hsupp.2.2 (u j) (hu j)))
    (fun i=>Finset.union_subset (Finset.union_subset (hsupp.1 false true (root i) (hroot i)) (hsupp.1 true true (root i) (hroot i)))
      (Finset.union_subset (hsupp.1 false false (root i) (hroot i)) (hsupp.1 true false (root i) (hroot i))))
    (fun i=>Finset.union_subset (hsupp.2.1 false (root i) (hroot i)) (hsupp.2.1 true (root i) (hroot i)))
  refine ⟨F,Q',hcross,havoid,?_⟩
  intro z
  convert hdegree z using 1 <;> ring
end Oberwolfach
