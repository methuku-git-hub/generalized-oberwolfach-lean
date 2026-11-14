module

public import Oberwolfach.MarkedSampleQuantitativeBoundarySelection
public import Oberwolfach.MarkedSampleProfileBoundarySelectionUniform

@[expose] public section
/-! Quantitative boundary selection uniformly over actual spoke densities
above a fixed lower bound. The sampled event and all profiles are unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_quantitative_boundary_selection_uniform (r:ℕ) (β aLo B pstar t₀ p₀ a gap omega:ℝ)
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
      1-1/(Fintype.card W:ℝ)^q-2/(Fintype.card (V⊕U):ℝ)^q≤
      (FiniteLaw.pi (fun _:Sym2 (V⊕U)=>FiniteLaw.retentionCoin p hp.le hp1)).probability
        (fun σ=>∀ τ:Sym2 (V⊕U)→Bool,
          (∀ x,((Finset.univ.filter (fun a:DirectedBoundaryEdge
            (markedActiveAuxTail tail ktail (H false) (H true)) (markedActiveAuxHead head khead (H false) (H true)) (ordinaryInnerVertices X Zinner)=>
            (markedActiveAuxTail tail ktail (H false) (H true) a.val=x∨markedActiveAuxHead head khead (H false) (H true) a.val=x)∧
            σ (markedActivePhysicalCoin tail head ktail khead π (H false) (H true) a.val)≠
              τ (markedActivePhysicalCoin tail head ktail khead π (H false) (H true) a.val))).card:ℝ)≤2*((p^9+p^3)*Fintype.card (V⊕U)))→
        ∀ Y:J→Finset W,(∀ j v,v∈Y j→H false (f v) (u j)∨H true (f v) (u j))→
          (∀ j,((Y j).filter (fun v=>H false (f v) (u j))).card=(r+4)*((Y j).filter (fun v=>H true (f v) (u j))).card)→
          (∀ j,((changed (Y j) ((Finset.univ.filter (fun v=>H false (f v) (u j)∨H true (f v) (u j))).filter
            (fun v=>σ s(Sum.inl (f v),Sum.inr (u j))=true))).card:ℝ)≤(p^9+p^3)*Fintype.card (V⊕U))→
        ∀ (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U),
          (∀ i,Disjoint (Y₀ i) (Y₁ i))→
          (∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(A₁ i).card=(Y₁ i).card)→
        ∀ Z:SimpleGraph (V⊕U),(∀ z,(Z.degree z:ℝ)≤p^3*Fintype.card (V⊕U))→
          (∀ i,((X₁ i).card:ℝ)+(gap/2)*p*Fintype.card (V⊕U)≤(Y₀ i).card)→
          (∀ i j,markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j⊆L (i,j))→
          (∀ i j,markedEndpointFiveHubs (Y₀ i) (Y₁ i) j⊆T (i,j))→
          (∀ i j,((changed (markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j)
            ((L (i,j)).filter (fun v=>σ (markedBoundaryEndpointCoin π (markedEndpointFiveRimType j)
              (markedEndpointFiveIncoming j) (root i) (Sum.inl v))=true))).card:ℝ)≤(p^9+p^3)*Fintype.card (V⊕U))→
          (∀ i j,((changed (markedEndpointFiveHubs (Y₀ i) (Y₁ i) j)
            ((T (i,j)).filter (fun u=>σ s(Sum.inl (root i),Sum.inr u)=true))).card:ℝ)≤(p^9+p^3)*Fintype.card (V⊕U))→
          (∀ i j,(a/2)*p*Fintype.card (V⊕U)≤(markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j).card∧
            ((markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j).card:ℝ)≤2*p*Fintype.card (V⊕U))→
          (∀ i j,(a/2)*p*Fintype.card (V⊕U)≤(markedEndpointFiveHubs (Y₀ i) (Y₁ i) j).card∧
            ((markedEndpointFiveHubs (Y₀ i) (Y₁ i) j).card:ℝ)≤2*p*Fintype.card (V⊕U))→
        (∀ j,(Y j).image f⊆markedBoundarySpokeRows (H false) (H true) X τ (u j))→
        (∀ i,A₀ i∪A₁ i∪(X₀ i∪X₁ i)⊆markedBoundaryRimNeighbours tail head ktail khead π X τ (root i))→
        (∀ i,Y₀ i∪Y₁ i⊆markedBoundarySpokeHubs (H false) (H true) Zinner τ (root i))→
        ∃ P:∀ j,MarkedHubFactorOn tail head ktail khead (r+4) π (3*d)
          (H false) (H true) (u j) ((Y j).image f),
        ∃ Q:∀ i,MarkedEndpointPairing (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) (H false) (H true) π (3*d),
        let G:J⊕I→SimpleGraph (V⊕U):=Sum.elim (fun j=>(P j).graph) (fun i=>(Q i).graph);
          (∀ i j,i≠j→Disjoint (G i) (G j)) ∧
          (∀ i,Disjoint (G i) Z) ∧
          ∀ z,((⨆ i,G i).degree z:ℝ)≤4*((14*p)*Fintype.card (V⊕U))) :=by
  obtain ⟨ε,hε,hnum⟩:=marked_boundary_selector_numerics p₀ a gap hp₀ ha hgap
  obtain ⟨η,ηEnd,ζ,hη,hηEnd,hζ,hsel⟩:=marked_sample_profile_boundary_selection_uniform r β aLo B pstar t₀ p₀ a ε
    hβ haLo hB hpstar ht₀ hp₀ hp₀1 ha ha1 hε
  obtain ⟨pmax,hpmax,hpmax8,hscale⟩:=hnum ζ omega hζ homega
  refine ⟨η,ηEnd,ζ,pmax,hη,hηEnd,hζ,hpmax,hpmax8,?_⟩
  intro d p hp hp1 hpp q
  obtain ⟨NS,hNS1,hNS⟩:=hsel d p hp hp1 q
  obtain ⟨NN,hNN⟩:=hscale p hp hpp d
  refine ⟨max NS NN,by omega,?_⟩
  intro t ht W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hWlo hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
    h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L T hsize
  have hWV:Fintype.card W≤Fintype.card V:=Fintype.card_le_of_injective f f.injective
  have hWn:Fintype.card W≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  obtain ⟨degree,tau,loss,htau,hdegree,hmargin,hgapnum,hcutloss,hloss,hclasses,hbudget,hmask,hchange⟩:=
    hNN (Fintype.card (V⊕U)) (by omega)
  have hlossW:loss≤ζ*p*Fintype.card W:=by
    apply hloss.trans
    have hh:=mul_le_mul_of_nonneg_left hWlo (show 0≤ζ*p by positivity)
    nlinarith only [hh]
  have hchangeW:(p^9+p^3)*Fintype.card (V⊕U)≤ζ*(p*Fintype.card W):=by
    apply hchange.trans
    have hh:=mul_le_mul_of_nonneg_left hWlo (show 0≤ζ*p by positivity)
    nlinarith only [hh]
  have hchangen:(p^9+p^3)*Fintype.card (V⊕U)≤ζ*(p*Fintype.card (V⊕U)):=by
    apply hchange.trans
    have hh:=mul_le_mul_of_nonneg_right homega1 (show 0≤ζ*p*Fintype.card (V⊕U) by positivity)
    nlinarith only [hh]
  have hevent:=hNS t ht W V U Gamma Color J I (by omega) hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload h hh errR errI heR heI heRsmall heIsmall
    hrowEnd hidxEnd w hQw hSw hwprob hsize
  apply hevent.trans
  apply finiteLaw_probability_mono
  intro σb hσ τ hτ Y hY hratio hYchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    Z hZ hgap' hsubR hsubH hchangeR hchangeH hsizeR hsizeH hYS hAS hBS
  apply hσ τ (fun x=>(hτ x).trans hmask) Y hY hratio
    (fun j=>(hYchange j).trans hchangeW) A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau loss htau Z (p^3*Fintype.card (V⊕U)) hZ hdegree hmargin
  · intro i
    linarith only [hgap' i,hgapnum]
  · exact hcutloss
  · nlinarith only [hlossW]
  · exact hsubR
  · exact hsubH
  · exact fun i j=>(hchangeR i j).trans hchangen
  · exact fun i j=>(hchangeH i j).trans hchangen
  · exact fun i j=>(hclasses _ (hsizeR i j).1 (hsizeR i j).2).1
  · exact fun i j=>(hclasses _ (hsizeH i j).1 (hsizeH i j).2).1
  · exact fun i j=>(hclasses _ (hsizeR i j).1 (hsizeR i j).2).2
  · exact fun i j=>(hclasses _ (hsizeH i j).1 (hsizeH i j).2).2
  · exact hbudget
  · exact hYS
  · exact hAS
  · exact hBS
end Oberwolfach
