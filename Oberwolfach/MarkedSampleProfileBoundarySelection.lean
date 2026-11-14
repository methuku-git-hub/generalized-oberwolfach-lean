module

public import Oberwolfach.MarkedSampleLocalBoundarySelection
public import Oberwolfach.MarkedFreshFiveEndpointProfiles

@[expose] public section

/-! The single boundary event now derives all five endpoint blocks from the
original row and index profiles, while the original inner weights supply
the factors. No independence between these events is needed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_profile_boundary_selection (r:ℕ) (β aLo B pstar t p₀ a ε:ℝ)
    (hβ:0<β) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar) (ht:0<t)
    (hp₀:0<p₀) (hp₀1:p₀≤1) (ha:0<a) (ha1:a≤1) (hε:0<ε):
    ∃ η ηEnd ζ:ℝ,0<η∧0<ηEnd∧0<ζ∧∀ (d:ℕ) (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,1≤N∧
    ∀ (W V U Gamma Color J I:Type) [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V]
      [Fintype U] [DecidableEq U] [Fintype Gamma] [Fintype Color]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
    N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
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
              τ (markedActivePhysicalCoin tail head ktail khead π (H false) (H true) a.val))).card:ℝ)≤p^2*Fintype.card (V⊕U)/2)→
        ∀ Y:J→Finset W,(∀ j v,v∈Y j→H false (f v) (u j)∨H true (f v) (u j))→
          (∀ j,((Y j).filter (fun v=>H false (f v) (u j))).card=(r+4)*((Y j).filter (fun v=>H true (f v) (u j))).card)→
          (∀ j,((changed (Y j) ((Finset.univ.filter (fun v=>H false (f v) (u j)∨H true (f v) (u j))).filter
            (fun v=>σ s(Sum.inl (f v),Sum.inr (u j))=true))).card:ℝ)≤ζ*(p*Fintype.card W))→
        ∀ (A₀ A₁ X₀ X₁:I→Finset V) (Y₀ Y₁:I→Finset U),
          (∀ i,Disjoint (Y₀ i) (Y₁ i))→
          (∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)→
          (∀ i,(A₁ i).card=(Y₁ i).card)→
        ∀ degree tau loss:ℝ,0<tau→
          ∀ (Z:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(Z.degree z:ℝ)≤δ)→
          2*tau+(2*(2*(3*d)+1):ℕ)≤degree→(2*(2*(3*d)+1):ℕ)<(p₀/4)*tau→
          (∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)→loss≤(p₀/4)*tau→loss≤ζ*(p*Fintype.card W)→
          (∀ i j,markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j⊆L (i,j))→
          (∀ i j,markedEndpointFiveHubs (Y₀ i) (Y₁ i) j⊆T (i,j))→
          (∀ i j,((changed (markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j)
            ((L (i,j)).filter (fun v=>σ (markedBoundaryEndpointCoin π (markedEndpointFiveRimType j)
              (markedEndpointFiveIncoming j) (root i) (Sum.inl v))=true))).card:ℝ)≤ζ*(p*Fintype.card (V⊕U)))→
          (∀ i j,((changed (markedEndpointFiveHubs (Y₀ i) (Y₁ i) j)
            ((T (i,j)).filter (fun u=>σ s(Sum.inl (root i),Sum.inr u)=true))).card:ℝ)≤ζ*(p*Fintype.card (V⊕U)))→
          (∀ i j,degree+loss≤p₀/2*(markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j).card)→
          (∀ i j,degree+loss≤p₀/2*(markedEndpointFiveHubs (Y₀ i) (Y₁ i) j).card)→
          (∀ i j,ε*(markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j).card≤tau)→
          (∀ i j,ε*(markedEndpointFiveHubs (Y₀ i) (Y₁ i) j).card≤tau)→
          4*((14*p)*Real.sqrt (14*p)*Fintype.card (V⊕U))+4*(Nat.ceil (4*((14*p)*Real.sqrt (14*p)*Fintype.card (V⊕U))):ℝ)+δ≤loss→
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
  obtain ⟨η,ζf,hη,hζf,hfactor⟩:=marked_sample_local_boundary_selection r β aLo B pstar t hβ haLo hB hpstar ht
  obtain ⟨ηEnd,ζe,hηEnd,hζe,hend⟩:=marked_fresh_five_endpoint_profiles p₀ a ε hp₀ hp₀1 ha ha1 hε
  let ζ:=min ζf ζe
  have hζ:0<ζ:=lt_min hζf hζe
  refine ⟨η,ηEnd,ζ,hη,hηEnd,hζ,?_⟩
  intro d p hp hp1 q
  obtain ⟨Nf,hNf1,hNf⟩:=hfactor p hp hp1 q
  obtain ⟨Ne,hNe⟩:=hend d q p hp hp1
  refine ⟨max Nf Ne,by omega,?_⟩
  intro W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hJ f ρ π hf P D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
    h hh errR errI heR heI heRsmall heIsmall hrowEnd hidxEnd w hQw hSw hwprob L T hsize
  have hWV:Fintype.card W≤Fintype.card V:=Fintype.card_le_of_injective f f.injective
  have hVI:Fintype.card I≤Fintype.card V:=Fintype.card_le_of_injective root root.injective
  have hIn:Fintype.card I≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  have hsel:=hNf W V U Gamma Color J I (by omega) hJ f ρ π hf P d D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ₀ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload
  have hep:=hNe V U Gamma Color I (by simp only [Fintype.card_sum];omega) hIn
    P π h X Zinner pr kr Q S g c errR errI σ₀ H w root hh heR heI heRsmall heIsmall
    hrowEnd hidxEnd hQw hSw hwprob hsize
  simp only [sub_sub] at hsel
  have hboth:=finiteLaw_two_events_lower _ _ _ _ _ hsel hep
  simp only [sub_sub] at hboth
  apply le_trans (b:=1-((1/(Fintype.card W:ℝ)^q+1/(Fintype.card (V⊕U):ℝ)^q)+1/(Fintype.card (V⊕U):ℝ)^q))
    (by ring_nf;exact le_rfl)
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro σb hσ τ hτ Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau loss htau Z δ hZ hdegree hmargin hgap hcutloss hloss
    hsubR hsubH hchangeR hchangeH hdegreeR hdegreeH htauR htauH hbudget hYS hAS hBS
  have hfacloss:loss≤ζf*(p*Fintype.card W):=
    hloss.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hblocks (i:I) (j:Fin 5):BipartiteBlockBounds
      (H (markedEndpointFiveLabelSpokeType j))
      (fun v=>v∈markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j)
      (fun u=>u∈markedEndpointFiveHubs (Y₀ i) (Y₁ i) j) (degree+loss) tau (2*(p₀/4)):=by
    have hh:=hσ.2 (i,j) (markedEndpointFiveRows (A₀ i) (A₁ i) (X₀ i) (X₁ i) j)
      (markedEndpointFiveHubs (Y₀ i) (Y₁ i) j) ⊥ (hsubR i j) (hsubH i j)
      ((hchangeR i j).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)))
      ((hchangeH i j).trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)))
      (by intro z;simpa using (show 0≤ζe*(p*Fintype.card (V⊕U)) by positivity))
    have hb:=hh.2.2 (degree+loss) tau (hdegreeR i j) (hdegreeH i j) (htauR i j) (htauH i j)
    have he:2*(p₀/4)=p₀/2:=by ring
    simpa only [SimpleGraph.bot_adj,not_false_eq_true,and_true,he] using hb
  apply hσ.1 τ hτ Y hY hratio
    (fun j=>(hchange j).trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)))
    A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked degree tau (p₀/4) loss htau (by positivity)
    Z δ hZ hdegree hmargin hgap hcutloss hfacloss
  · exact fun i=>hblocks i 0
  · exact fun i=>hblocks i 1
  · exact fun i=>hblocks i 2
  · exact fun i=>hblocks i 3
  · exact fun i=>hblocks i 4
  · exact hbudget
  · exact hYS
  · exact hAS
  · exact hBS

end Oberwolfach
