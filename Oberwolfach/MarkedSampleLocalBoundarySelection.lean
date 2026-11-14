module

public import Oberwolfach.MarkedSampleFreshInnerHubEvent
public import Oberwolfach.MarkedSampleArcEmbedding
public import Oberwolfach.MarkedLocalDomainBoundarySelection
public import Oberwolfach.MarkedHubFactorHostLift

@[expose] public section

/-! Boundary factors and endpoint assignments from the actual fixed sample.
Inner row profiles, configuration counts and fixed potential loads supply
the factor hypotheses. One later physical boundary sample works for all
permitted subsequent class choices, masks and forbidden graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 26000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_local_boundary_selection (r:ℕ) (β aLo B pstar t:ℝ)
    (hβ:0<β) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar) (ht:0<t):
    ∃ η ζ:ℝ,0<η∧0<ζ∧∀ (p:ℝ) (hp:0<p) (hp1:p≤1) (q:ℕ),∃ N:ℕ,1≤N∧
    ∀ (W V U Gamma Color J I:Type) [Fintype W] [LinearOrder W] [Fintype V] [LinearOrder V]
      [Fintype U] [DecidableEq U] [Fintype Gamma] [Fintype Color]
      [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I],
    N≤Fintype.card W→Fintype.card J≤(Fintype.card W)^2→
    ∀ (f:W↪oV) (ρ:Equiv.Perm W) (π:Equiv.Perm V),(∀ x,f (ρ x)=π (f x))→
    ∀ (P:SimpleGraph V) (d:ℕ) (D τweight pr kr sr:ℝ),
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
      1-1/(Fintype.card W:ℝ)^q-1/(Fintype.card (V⊕U):ℝ)^q≤
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
        ∀ degree tau lam loss:ℝ,0<tau→0<lam→
          ∀ (Z:SimpleGraph (V⊕U)) (δ:ℝ),(∀ z,(Z.degree z:ℝ)≤δ)→
          2*tau+(2*(2*(3*d)+1):ℕ)≤degree→(2*(2*(3*d)+1):ℕ)<lam*tau→
          (∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)→loss≤lam*tau→loss≤ζ*(p*Fintype.card W)→
          (∀ i,BipartiteBlockBounds (H false) (fun a=>a∈A₁ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (H false) (fun a=>a∈A₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (H true) (fun a=>a∈X₁ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (H false) (fun a=>a∈X₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))→
          (∀ i,BipartiteBlockBounds (H false) (fun a=>a∈X₀ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))→
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
  obtain ⟨η,ζ,hη,hζ,hfactor⟩:=marked_sample_fresh_inner_hub_event r β aLo B pstar t hβ haLo hB hpstar ht
  refine ⟨η,ζ,hη,hζ,?_⟩
  intro p hp hp1 q
  obtain ⟨Nf,hNf1,hNf⟩:=hfactor p hp hp1 q
  obtain ⟨Nm,hNm⟩:=select_mixed_marked_boundary_avoiding (14*p) (by positivity)
  obtain ⟨Ns,hNs⟩:=marked_boundary_robust_support_event p hp hp1 q
  refine ⟨max Nf (max Nm Ns),by omega,?_⟩
  intro W V U Gamma Color J I _ _ _ _ _ _ _ _ _ _ _ _ hn hJ f ρ π hf P d D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw σ H u root Zinner hu hroot hd hsep
    Q S g c hQ hrows hconfigs hload E K tail head ktail khead X
  have hWV:Fintype.card W≤Fintype.card V:=Fintype.card_le_of_injective f f.injective
  have hn':max Nm Ns≤Fintype.card (V⊕U):=by simp only [Fintype.card_sum];omega
  have hlocsep:∀ j x z,H false (f x) (u j)→H true (f z) (u j)→x≠ρ z:=by
    intro j x z hx hz he
    apply hsep (u j) (f x) (f z) hx hz
    rw [←hf z,he]
  have hfac:=hNf W V U Gamma Color J (by omega) hJ f.toEmbedding ρ π hf (P.comap f) d D τweight pr kr sr
    hDlo hDhi hpr hkr hsr hpr1 hkr1 hsr1 weight hw (rawMarkedRestrictVertices f σ) (fun b x u=>H b (f x) u) u
    (fun j x=>hd (u j) (f x)) hlocsep Q S g c hQ hrows hconfigs hload
  have hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π):=
    markedSampleArc_physical_injective P π (3*d) _
  have hsupp:=hNs V U E K (by omega) tail head ktail khead π (H false) (H true) X Zinner hphys
  have hboth:=finiteLaw_two_events_lower _ _ _ _ _ hfac hsupp
  apply hboth.trans
  apply finiteLaw_probability_mono
  intro σb hσ τ hτ Y hY hratio hchange A₀ A₁ X₀ X₁ Y₀ Y₁ hYY hbalA hbalX hmarked
    degree tau lam loss htau hlam Z δ hZ hdegree hmargin hgap hcutloss hloss
    B₁ B₂ B₃ B₄ B₅ hbudget hYS hAS hBS
  obtain ⟨_,hpair,hmem⟩:=hσ.2 τ hτ
  obtain ⟨hpair',hmem'⟩:=marked_boundary_selection_supports tail head ktail khead π (H false) (H true) X Zinner τ
    u root hu hroot (fun j=>(Y j).image f) A₀ A₁ X₀ X₁ Y₀ Y₁ hYS hAS hBS _ _ hpair hmem
  apply hNm V U E K J I (by omega) tail head ktail khead (r+4) (3*d) π
    (H false) (H true) u (fun j=>(Y j).image f) A₀ A₁ X₀ X₁ Y₀ Y₁
    (fun j=>hsep (u j)) hYY hbalA hbalX hmarked degree tau lam loss htau hlam Z δ hZ
    hdegree hmargin hgap hcutloss B₁ B₂ B₃ B₄ B₅ hbudget _ hpair' hmem'
  intro j F hF
  obtain ⟨R,hR⟩:=hσ.1 j (Y j) (hY j) (hratio j) (hchange j) F (fun v=>(hF v).trans hloss)
  have h₀:∀ v u,spokeRelationImage f.toEmbedding (fun x=>H false (f x)) v u→H false v u:=by
    rintro v u ⟨x,hx,hH⟩;exact hx ▸ hH
  have hK:∀ v u,spokeRelationImage f.toEmbedding (fun x=>H true (f x)) v u→H true v u:=by
    rintro v u ⟨x,hx,hH⟩;exact hx ▸ hH
  obtain ⟨R',hRrim,hRgraph⟩:=marked_hub_factor_host_lift
    _ _ _ _ tail head ktail khead
    (markedSampleArcEmbedding f π ρ hf P (3*d) σ false)
    (markedSampleArcEmbedding f π ρ hf P (3*d) σ true)
    (fun _=>rfl) (fun _=>rfl) (fun _=>rfl) (fun _=>rfl)
    (r+4) (3*d) π _ _ (H false) (H true) h₀ hK (u j) _ R
  exact ⟨R',by rw [hRrim];exact hR⟩

end Oberwolfach
