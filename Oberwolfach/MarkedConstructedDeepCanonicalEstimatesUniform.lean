module

public import Oberwolfach.MarkedConstructedDeepActiveEstimatesOrderedUniform
public import Oberwolfach.MarkedProtectedSeparateDeletion
public import Oberwolfach.MarkedSampleBalanceCongruence
public import Oberwolfach.MarkedProtectedSampleBalanceBounds
public import Oberwolfach.MarkedTwoStageActiveBalanceBounds

@[expose] public section

/-! The deep-cover constants precede the inner correction tolerance.
 The actual inner correction and deep packings also supply the quantitative
balance estimates at every root of the active sample. All parameter choices
and constructed packings are the same as in the exact-balance constructor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_constructed_deep_canonical_estimates_uniform
    (r:ℕ) (hr:2≤r) (omega₀ t₀ rho₀ gamma eta:ℝ)
    (ho₀:0<omega₀) (ht₀:0<t₀) (ht₀1:t₀≤1) (hrho₀:0<rho₀) (hrho₀1:rho₀≤1)
    (hg:0<gamma) (hg1:gamma≤1) (heta:0<eta) (hetaSmall:eta≤t₀*(t₀*omega₀/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (hβt₀:β≤t₀/2) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar)
:
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ etaEmax:ℝ,0<etaEmax ∧     ∀ omegaI hIcut deltaI mu:ℝ,0<omegaI→0<hIcut→0<deltaI→deltaI<1/4→0<mu→
    ∀ etaE:ℝ,0<etaE→etaE≤etaEmax→∃ etaBal:ℝ,0<etaBal ∧ ∃ NI:ℕ,∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ omega t rho:ℝ,omega₀≤omega → t₀≤t → rho₀≤rho → rho≤1 → (((r+1)+3:ℕ):ℝ)*t≤1 →
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
    (∀ x u,¬(H false x u∧H true x u))→
    (∀ u x z,H false x u→H true z u→x≠π z)→
    ∀ (I T:Finset V) (J W:Finset U),T⊆I→W⊆J→
    (∀ x,π x∈I↔x∈I)→(∀ x,π x∈T↔x∈T)→
    (I.card:ℝ)≤zeta*Fintype.card V→(J.card:ℝ)≤zeta*Fintype.card V→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    let S:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    NI≤I.card→ omegaI*I.card≤J.card→J.card≤I.card→
    (T.card:ℝ)≤hIcut*I.card→(W.card:ℝ)≤hIcut*J.card→
    let EI:={e:E₀ // tail e∈I∧head e∈I}
    let KI:={e:E₁ // ktail e∈I∧khead e∈I}
    let tI:=fun e:EI=>(⟨tail e.val,e.property.1⟩:I)
    let hI':=fun e:EI=>(⟨head e.val,e.property.2⟩:I)
    let ktI:=fun e:KI=>(⟨ktail e.val,e.property.1⟩:I)
    let khI:=fun e:KI=>(⟨khead e.val,e.property.2⟩:I)
    let H0I:=fun v:I=>fun u:J=>H false v.val u.val
    let HKI:=fun v:I=>fun u:J=>H true v.val u.val
    (∀ v,|occurrenceDegree (Sum.elim tI ktI) v-
      (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤etaBal*I.card)→
    (∀ v,|occurrenceDegree (Sum.elim hI' khI) v-
      (∑ u,if H0I v u then (1:ℝ) else 0)-(∑ u,if HKI v u then (1:ℝ) else 0)|≤etaBal*I.card)→
    (∀ v,|occurrenceDegree khI v-(∑ u,if HKI v u then (1:ℝ) else 0)|≤etaBal*I.card)→
    (∀ u,|(∑ v,if H0I v u then (1:ℝ) else 0)-(r+4:ℕ)*(∑ v,if HKI v u then (1:ℝ) else 0)|≤etaBal*I.card)→
    BipartiteLargeCut (occurrenceMultiplicity tI hI') deltaI (2*hIcut)→
    BipartiteLargeCut (occurrenceMultiplicity ktI khI) deltaI (2*hIcut)→
    BipartiteLargeCut (relationMultiplicity H0I) deltaI (2*hIcut)→
    BipartiteLargeCut (relationMultiplicity HKI) deltaI (2*hIcut)→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ S (r+4)→
    ∃ (DA:Finset (E₀⊕E₁)) (DS₀:Finset (V×U)),
    (∀ a∈DA,Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I)∧
    (∀ z∈DS₀,z.1∈I∧z.2∈J∧z∈S)∧
    (∀ x,((DA.filter (fun a=>x=Sum.elim tail ktail a∨x=Sum.elim head khead a)).card:ℝ)≤mu*I.card)∧
    (∀ x,((DS₀.filter (fun z=>x=z.1)).card:ℝ)≤mu*I.card)∧
    (∀ u,((DS₀.filter (fun z=>z.2=u)).card:ℝ)≤mu*I.card)∧
    (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedInnerResource T W)=∅∧
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS (r+4)∧
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
    ∃ M:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
    (∀ X∈M,∀ Y∈M,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))∧
    (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS₀).filter (markedStarResource T W)∧
    (∀ x,((markedPackingRimGraph M).degree x:ℝ)≤24*etaE*Fintype.card V)∧
    (∀ x,((Finset.univ.filter (markedPackingSpokes M x)).card:ℝ)≤6*etaE*Fintype.card V)∧
    (∀ u,((Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card:ℝ)≤3*(r+5)*etaE*Fintype.card V)∧
    M.biUnion markedWheelArcs⊆Finset.univ\KA∧M.biUnion markedWheelSpokePairs⊆S\KS∧
    let DR:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)
    let DS:=markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)
    ∃ M_D:Finset (MarkedWheel tail head ktail khead (r+4) π (3*d) (H false) (H true)),
      (∀ X∈M_D,∀ Y∈M_D,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y)) ∧
      (∀ x∉I,(markedPackingRimGraph M_D).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card) ∧
      (∀ x∉I,(Finset.univ.filter (markedPackingSpokes M_D x)).card≤W.card+T.card*(K+4)) ∧
      (∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes M_D x u)).card≤T.card*(r+5)) ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅ ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅ ∧
      Disjoint (markedPackingRimGraph M_D) DR ∧
      (∀ x u,markedPackingSpokes M_D x u→¬DS.Adj (Sum.inl x) (Sum.inr u))∧
      (∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1→
        ¬DR.Adj x (if mark then π y else y)→markedStarResource T W (Sum.inl ({x,if mark then π y else y}:Finset V))→
        Sum.inl ({x,if mark then π y else y}:Finset V)∈M_D.biUnion markedWheelPhysicalResources)∧
      (∀ mark x u,H mark x u→¬DS.Adj (Sum.inl x) (Sum.inr u)→markedStarResource T W (Sum.inr (x,u))→
        Sum.inr (x,u)∈M_D.biUnion markedWheelPhysicalResources)∧
      ∀ (A B:Type) [Fintype A] [Fintype B] [LinearOrder A] [DecidableEq B],
      ∀ (f:A↪oV) (g:B↪U) (ρA:Equiv.Perm A),(∀ x,f (ρA x)=π (f x))→
      (∀ x,x∈Finset.univ.image f↔x∉T)→(∀ u,u∈Finset.univ.image g↔u∉W)→
      ∀ (XA:Finset A) (ZA:Finset B),(∀ x,f x∈I↔x∈XA)→(∀ u,g u∈J↔u∈ZA)→
      let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ (markedPackingRimGraph M⊔markedPackingRimGraph M_D).edgeFinset)
      let HA:=fun b x u=>markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (M.biUnion markedWheelSpokePairs)⊔markedFiniteSpokeGraph (M_D.biUnion markedWheelSpokePairs)) b (f x) (g u)
      let EA₀:=MarkedSampleArc (P.comap f) ρA (3*d) (fun e=>σA (Sum.inl e)) false
      let EA₁:=MarkedSampleArc (P.comap f) ρA (3*d) (fun e=>σA (Sum.inl e)) true
      MarkedOutsideBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2)
        (fun e:EA₁=>e.val.1) (fun e=>e.val.2) (HA true) Finset.univ
        (Finset.univ.filter (fun z:A×B=>HA false z.1 z.2∨HA true z.1 z.2)) (r+4) XA ZA ∧
      ∀ εI εT:ℝ,0≤εT→
      (∀ z i,|markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S (r+4) I J z i|≤εI)→
      (∀ z i,|markedFiniteDomainBalance tail head ktail khead (H true) Finset.univ S (r+4) T W z i|≤εT)→
      ∀ (z:A⊕B) (i:Fin 4),
      |markedFiniteBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2) (fun e:EA₁=>e.val.1) (fun e=>e.val.2)
        (HA true) Finset.univ (Finset.univ.filter (fun s:A×B=>HA false s.1 s.2∨HA true s.1 s.2)) (r+4) z i|
        ≤εT+((r+4:ℕ)+2)*(mu*I.card) ∧
      |markedFiniteDomainBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2) (fun e:EA₁=>e.val.1) (fun e=>e.val.2)
        (HA true) Finset.univ (Finset.univ.filter (fun s:A×B=>HA false s.1 s.2∨HA true s.1 s.2)) (r+4) XA ZA z i|
        ≤εI+εT+((r+4:ℕ)+2)*(4*(24*etaE*Fintype.card V)+3*(r+5)*etaE*Fintype.card V):=by
  obtain ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,etaEmax,hemax,hbase⟩:=
    marked_constructed_deep_active_estimates_ordered_uniform r hr omega₀ t₀ rho₀ gamma eta ho₀ ht₀ ht₀1 hrho₀ hrho₀1 hg hg1 heta hetaSmall
      β aLo B pstar hβ hβt₀ haLo hB hpstar
  refine ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,etaEmax,hemax,?_⟩
  intro omegaI hIcut deltaI mu hoI hhI hdI hdIs hmu
  have hbase:=hbase omegaI hIcut deltaI mu hoI hhI hdI hdIs hmu
  intro etaE hetaE hcap
  obtain ⟨etaBal,hetaBal,NI,hall⟩:=hbase etaE hetaE hcap
  refine ⟨etaBal,hetaBal,NI,?_⟩
  intro d hd
  obtain ⟨N,hN,hall⟩:=hall d hd
  refine ⟨N,hN,?_⟩
  intro omega t rho hω htlo hρ hrho1 hst
  intro V U Γ Color _ _ _ _ _ _ hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
    D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload hH hshift I T J W hTI hWJ hI hT hIsize hJsize
    E₀ E₁ tail head ktail khead S hNI hoIn hJI hTsize hWsize EI KI tI hI' ktI khI H0I HKI
    hbp hbm hbk hbw hc0 hcK hcs0 hcsK houter
  obtain ⟨DA,DS₀,hDA,hDS,hDAdeg,hDSrow,hDScol,havoid,hinner,
      ME,hME,hMEinner,hMER,hMEV,hMEU,hMEA,hMES,MD,hMD,hMDR,hMDV,hMDU,hMDinner,hMDstar,hMDsupport,hMDA,hMDS,hactive⟩:=
    hall omega t rho hω htlo hρ hrho1 hst V U Γ Color hn hUn hU P π hdeg hparent q s g j hq hs σ H hrows hindices
      D τ p k s₀ hDlo hDhi hp hk hs₀ hp1 hk1 hs₁ weight hw hconfigs hload hH hshift I T J W hTI hWJ hI hT hIsize hJsize
      hNI hoIn hJI hTsize hWsize hbp hbm hbk hbw hc0 hcK hcs0 hcsK houter
  let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
  let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS₀
  let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
  let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W)
  let DR:=markedSampleArcSetGraph P π d σ (KA∪ME.biUnion markedWheelArcs)
  let DS:=markedFiniteSpokeGraph (KS∪ME.biUnion markedWheelSpokePairs)
  let ND:=MD.image (markedPhysicalDeletedSampleWheelLift P π d (r+4) σ DR DS H)
  obtain ⟨hNDres,hND,hNDR,hNDS⟩:=markedPhysicalDeletedSamplePacking_lift P π d (r+4) σ DR DS H MD hMD
  obtain ⟨hNDgraph,hNDspokes⟩:=markedPackingResourceEquality_graphs ND MD hNDres
  have hNDpairs:=markedPackingResourceEquality_spokePairs ND MD hNDres
  have hNDRdeg:∀ x∉I,(markedPackingRimGraph ND).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card:=by
    intro x hx
    simpa only [←SimpleGraph.ncard_neighborSet,hNDgraph] using hMDR x hx
  have hNDV:∀ x∉I,(Finset.univ.filter (markedPackingSpokes ND x)).card≤W.card+T.card*(K+4):=by
    intro x hx
    simpa only [←Set.ncard_coe_finset,Finset.coe_filter,hNDspokes] using hMDV x hx
  have hNDU:∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes ND x u)).card≤T.card*(r+5):=by
    intro u hu
    simpa only [←Set.ncard_coe_finset,Finset.coe_filter,hNDspokes] using hMDU u hu
  have hNDinner:(ND.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅:=by rw [hNDres];exact hMDinner
  have hNDstar:(ND.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅:=by rw [hNDres];exact hMDstar
  have hDRcover:∀ mark x y,markedPhysicalRim P π (3*d) (fun e=>σ (Sum.inl e)) mark x y=1→
      ¬DR.Adj x (if mark then π y else y)→markedStarResource T W (Sum.inl ({x,if mark then π y else y}:Finset V))→
      Sum.inl ({x,if mark then π y else y}:Finset V)∈ND.biUnion markedWheelPhysicalResources:=by
    intro mark x y he hd hstar
    have he':markedPhysicalRim P π (3*d) (fun e=>rawMarkedDeleteRims σ DR.edgeFinset (Sum.inl e)) mark x y=1:=
      (markedPhysicalRim_delete_iff P π d σ DR.edgeFinset mark x y).mpr ⟨he,by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using hd⟩
    rw [hNDres]
    cases mark with
    | false=>exact hMDA (Sum.inl ⟨(x,y),he'⟩) hstar
    | true=>exact hMDA (Sum.inr ⟨(x,y),he'⟩) hstar
  have hDScover:∀ mark x u,H mark x u→¬DS.Adj (Sum.inl x) (Sum.inr u)→markedStarResource T W (Sum.inr (x,u))→
      Sum.inr (x,u)∈ND.biUnion markedWheelPhysicalResources:=by
    intro mark x u he hd hstar
    rw [hNDres]
    apply hMDS x u _ hstar
    cases mark with
    | false=>exact Or.inl ⟨he,hd⟩
    | true=>exact Or.inr ⟨he,hd⟩
  refine ⟨DA,DS₀,hDA,hDS,hDAdeg,hDSrow,hDScol,havoid,hinner,
    ME,hME,hMEinner,hMER,hMEV,hMEU,hMEA,hMES,ND,hND,hNDRdeg,hNDV,hNDU,hNDinner,hNDstar,hNDR,hNDS,hDRcover,hDScover,?_⟩
  intro A B _ _ _ _ f gA ρA hf hfT hgW XA ZA hXA hZA
  have hfnot:∀ x,f x∉T:=fun x=>(hfT _).mp (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)
  have hgnot:∀ u,gA u∉W:=fun u=>(hgW _).mp (Finset.mem_image.mpr ⟨u,Finset.mem_univ _,rfl⟩)
  have hsp:=markedFiniteSpokeGraph_packing_degrees ME
  obtain ⟨hσA,hHA,_⟩:=marked_protected_active_deletion_separate f gA P π d σ H I T J W hT hfnot hgnot MD hMDstar
    (markedPackingRimGraph ME) (markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs))
    (24*etaE*Fintype.card V) (6*etaE*Fintype.card V) (3*(r+5)*etaE*Fintype.card V)
    (2*W.card+T.card*(4*(K+4))+2*T.card:ℕ) (W.card+T.card*(K+4):ℕ) (T.card*(r+5):ℕ)
    hMER (fun x=>by rw [hsp.1];exact hMEV x) (fun u=>by rw [hsp.2];exact hMEU u)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (fun x hx=>Nat.cast_le.mpr (hMDR x hx)) (fun x hx=>Nat.cast_le.mpr (hMDV x hx)) (fun u hu=>Nat.cast_le.mpr (hMDU u hu))
    KA KS (fun a ha=>(Finset.mem_filter.mp ha).2) (fun z hz=>(Finset.mem_filter.mp hz).2)
  have hDRedge:DR.edgeFinset=(markedSampleArcSetGraph P π d σ KA⊔markedPackingRimGraph ME).edgeFinset:=by
    apply Finset.coe_injective
    simp only [SimpleGraph.coe_edgeFinset,DR,markedSampleArcSetGraph_union,markedSampleArcSetGraph_packing]
  have hDRnext:(markedPackingRimGraph ME⊔markedPackingRimGraph MD).edgeFinset=
      (markedPackingRimGraph ME⊔markedPackingRimGraph ND).edgeFinset:=by
    apply Finset.coe_injective;simp only [SimpleGraph.coe_edgeFinset,hNDgraph]
  have hDSprior:DS=markedFiniteSpokeGraph KS⊔markedFiniteSpokeGraph (ME.biUnion markedWheelSpokePairs):=by
    dsimp [DS];rw [markedFiniteSpokeGraph_union]
  have hDSnext:markedFiniteSpokeGraph (ND.biUnion markedWheelSpokePairs)=markedFiniteSpokeGraph (MD.biUnion markedWheelSpokePairs):=by rw [hNDpairs]
  rw [hDRnext] at hσA
  rw [←hDRedge] at hσA
  rw [←hDSprior] at hHA
  conv at hHA => rhs; rw [←hDSnext]
  obtain ⟨hOutside,hBalance⟩:=hactive A B f gA ρA hf hfT hgW XA ZA hXA hZA
  constructor
  · exact (marked_sample_outside_balance_congr (P.comap f) ρA d (r+4) _ _ _ _ hσA hHA XA ZA).mp hOutside
  · intro εI εT hεT hAI hAT z i
    have hh:=hBalance εI εT hεT hAI hAT z i
    obtain ⟨he,hf⟩:=marked_sample_finite_balance_congr (P.comap f) ρA d (r+4) _ _ _ _ hσA hHA XA ZA z i
    rw [he,hf] at hh
    exact hh

end Oberwolfach
