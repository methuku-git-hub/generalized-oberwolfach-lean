module

public import Oberwolfach.MarkedSampleDeepCoverAfterDeletion
public import Oberwolfach.MarkedReservedDeletedSampleAvoidance

@[expose] public section
/-! The sampled deep-cover theorem may reserve a bounded physical resource
set in addition to the previous deletion graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 16384
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_sample_deep_cover_preserving_reserved_resources
    (r:ℕ) (hr:1≤r) (omega t rho gamma eta:ℝ)
    (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1) (hg:0<gamma) (hg1:gamma≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1) (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (hβt:β≤t/2) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ delta:ℝ,0<delta ∧ ∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→(Fintype.card U:ℝ)≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    (∀ x,|(P.degree x:ℝ)-2*Fintype.card U/rho|≤eps*Fintype.card V)→
    ∀ (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    (∀ u,q u g=t)→(∀ u,s u j=(((r+1)+3:ℕ):ℝ)*t)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d ((r+1)+11) Finset.univ (rho*((((r+1)+3:ℕ):ℝ)*t)/2) (rho*t/2)
      q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d ((r+1)+11) Finset.univ q s g j (eps*Fintype.card V) σ H→
    ∀ (D τ p k s₀:ℝ),(Fintype.card V:ℝ)/2≤D→D≤2*Fintype.card V→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    ∀ weight:(Fin (r+4+1)→V)→ℝ,SuccessorSequenceWeightConditions P π (3*d) D τ aLo B weight→
    MarkedLocalConfigurationsWithSpokes r P π d Finset.univ (2*β) (2*β) σ H→
    MarkedLocalSpokeLoadsWithSpokes P π d (r+4) D p k s₀ weight (θ/2) σ H→
    ∀ (C:Finset (Finset V⊕(V×U))), (C.card:ℝ)≤delta*Fintype.card V→
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤delta*Fintype.card V)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V)→
    let DRall:=DR⊔physicalEdgeGraph (markedReservedRimPairs C)
    let DSall:=DS⊔markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let edgeInst:Fintype DRall.edgeSet:=@SimpleGraph.fintypeEdgeSet V DRall (Sym2.instFintype)
      (fun x y=>Classical.propDecidable (DRall.Adj x y))
    let σ':=rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V DRall edgeInst)
    let H':=markedDeletePhysicalSpokes H DSall
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (F:Finset V),(∀ x,π x∈F↔x∈F)→((Fᶜ).card:ℝ)≤zeta*Fintype.card V→
    ∀ hHub:ℕ,(hHub:ℝ)≤zeta*Fintype.card V→
    ∀ u:Fin hHub→U,Function.Injective u→
    (∀ i x,¬(H' false x (u i)∧H' true x (u i)))→
    (∀ i x z,H' false x (u i)→H' true z (u i)→x≠π z)→
    (∀ i,Fintype.card (hubNeighbourClass (H' false) (H' true) (u i) false)=
      (r+4)*Fintype.card (hubNeighbourClass (H' false) (H' true) (u i) true))→
    (∀ i x,H' false x (u i)∨H' true x (u i)→x∈F)→
    ∀ (m:ℕ) (v:Fin m→V),Function.Injective v→(m:ℝ)≤zeta*Fintype.card V→(∀ i,v i∉F)→
    (∀ i u,¬(H' false (v i) u∧H' true (v i) u))→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim head khead a=v i→Sum.elim tail ktail a∈F)→
    (∀ i,∀ a:E₀⊕E₁,Sum.elim tail ktail a=v i→Sum.elim head khead a∈F)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun z:V×U=>(H' false z.1 z.2∨H' true z.1 z.2)∧z.1=v i)).card)→
    (∀ i,(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim head khead a=v i∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>H' true z.1 z.2∧z.1=v i)).card)→
    let Y₀:=fun i=>Finset.univ.filter (H' false (v i))
    let Y₁:=fun i=>Finset.univ.filter (H' true (v i))
    let ain:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ true (v i) σ'
    let xout:=fun i=>markedEndpointTaggedArcEmbedding P π d Finset.univ false (v i) σ'
    (∀ i,Disjoint (Y₀ i∪Y₁ i) (Finset.univ.image u))→
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H' false) (H' true)),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (∀ x,(spanningRestriction (markedPackingRimGraph M) F).degree x≤2*hHub+m*(4*(K+4))) ∧
      (∀ x∈F,(markedPackingRimGraph M).degree x≤2*hHub+m*(4*(K+4))+2*m) ∧
      (∀ x∈F,(Finset.univ.filter (markedPackingSpokes M x)).card≤hHub+m*(K+4)) ∧
      (∀ z∉Finset.univ.image u,(Finset.univ.filter (fun x=>markedPackingSpokes M x z)).card≤m*(r+5)) ∧
      (∀ (I:Finset V) (J:Finset U),Disjoint F I→(∀ x,π x∈I↔x∈I)→
        (∀ i,Disjoint (Y₀ i∪Y₁ i) J)→
        (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅) ∧
      (∀ W∈M,(W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
        ∃ i,W.2.val∈Y₀ i∪Y₁ i∧markedWheelRows W⊆insert (v i) F∧v i∈markedWheelRows W) ∧
      (∀ T:Finset V,T⊆Finset.univ.image v→(∀ x,π x∈T↔x∈T)→
        (∀ a:E₀⊕E₁,markedStarResource T (Finset.univ.image u)
          (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
          Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources) ∧
        (∀ x z,H' false x z∨H' true x z→markedStarResource T (Finset.univ.image u) (Sum.inr (x,z))→
          Sum.inr (x,z)∈M.biUnion markedWheelPhysicalResources)) ∧
      Disjoint C (M.biUnion markedWheelPhysicalResources) :=by
  obtain ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,delta,hdelta,hcover⟩:=
    marked_sample_deep_cover_after_physical_deletion r hr omega t rho gamma eta ho ht hrho hrho1 hg hg1
      hst heta hetaSmall β aLo B pstar hβ hβt haLo hB hpstar
  refine ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,delta/2,by positivity,?_⟩
  intro d hd
  obtain ⟨N,hN,hcover⟩:=hcover d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload C hCsize DR DS hDR hDSr hDSc DRall DSall edgeInst σ' H' E₀ E₁ tail head ktail khead
  have hgraphs:=marked_reserved_resource_graphs C
  have hDRall:∀ x,(DRall.degree x:ℝ)≤delta*Fintype.card V:=by
    intro x
    have hg:((DR⊔physicalEdgeGraph (markedReservedRimPairs C)).degree x:ℝ)≤
        (DR.degree x:ℝ)+(physicalEdgeGraph (markedReservedRimPairs C)).degree x:=by
      exact_mod_cast graph_degree_sup_le DR (physicalEdgeGraph (markedReservedRimPairs C)) x
    have hc:((physicalEdgeGraph (markedReservedRimPairs C)).degree x:ℝ)≤delta/2*Fintype.card V:=
      (Nat.cast_le.mpr (hgraphs.2.2.1 x)).trans hCsize
    dsimp only [DRall]
    linarith [hDR x]
  have hDSall:∀ z,(DSall.degree z:ℝ)≤delta*Fintype.card V:=by
    intro z
    have hg:((DS⊔markedFiniteSpokeGraph (markedReservedSpokePairs C)).degree z:ℝ)≤
        (DS.degree z:ℝ)+(markedFiniteSpokeGraph (markedReservedSpokePairs C)).degree z:=by
      exact_mod_cast graph_degree_sup_le DS (markedFiniteSpokeGraph (markedReservedSpokePairs C)) z
    have hc:((markedFiniteSpokeGraph (markedReservedSpokePairs C)).degree z:ℝ)≤delta/2*Fintype.card V:=
      (Nat.cast_le.mpr (hgraphs.2.2.2 z)).trans hCsize
    have hd:((DS.degree z):ℝ)≤delta/2*Fintype.card V:=by cases z with | inl x=>exact hDSr x | inr u=>exact hDSc u
    dsimp only [DSall]
    linarith
  intro F hF hFc hHub hhub u hu hdis hsep hratio hneigh m v hv hm hvF hdisRow hinc hout hdir hbal hmark Y₀ Y₁ ain xout hYavoid
  obtain ⟨M,hM,hR,hFR,hFV,hSU,hInner,hShape,hCover⟩:=hcover V U Γ Color hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload DRall DSall (by intro x;simpa only [←SimpleGraph.ncard_neighborSet] using hDRall x)
    (by intro x;simpa only [←SimpleGraph.ncard_neighborSet] using hDSall (Sum.inl x))
    (by intro u;simpa only [←SimpleGraph.ncard_neighborSet] using hDSall (Sum.inr u)) F hF hFc hHub hhub u hu hdis hsep hratio hneigh
    m v hv hm hvF hdisRow hinc hout hdir hbal hmark hYavoid
  have havoid:Disjoint C (M.biUnion markedWheelPhysicalResources):=
    marked_deleted_sample_packing_avoids_reserved_resources P π d (r+4) (by omega) (by omega) σ H C DRall DSall
      le_sup_right le_sup_right M
  exact ⟨M,hM,hR,hFR,hFV,hSU,hInner,hShape,hCover,havoid⟩
end Oberwolfach
