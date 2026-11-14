module

public import Oberwolfach.MarkedConstructedDeepActiveBalanceOrdered
public import Oberwolfach.MarkedStarCoverActiveBalance

@[expose] public section

/-! Construct the inner correction and both deep-stage packings in one
caller. The small correction is derived from the actual inner balances and
cuts, and every order-independent constant is chosen before the separation
radius. No correction set or deep-stage packing is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 48000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_constructed_deep_active_balance_controlled
    (r:ℕ) (hr:2≤r) (omega t rho gamma eta:ℝ)
    (ho:0<omega) (ht:0<t) (hrho:0<rho) (hrho1:rho≤1) (hg:0<gamma) (hg1:gamma≤1)
    (hst:(((r+1)+3:ℕ):ℝ)*t≤1) (heta:0<eta) (hetaSmall:eta≤t*(t*omega/2)/32)
    (β aLo B pstar:ℝ) (hβ:0<β) (hβt:β≤t/2) (haLo:0<aLo) (hB:0≤B) (hpstar:0<pstar)
    (omegaI hIcut deltaI mu:ℝ) (hoI:0<omegaI) (hhI:0<hIcut) (hdI:0<deltaI) (hdIs:deltaI<1/4) (hmu:0<mu):
    ∃ eps:ℝ,0<eps ∧ ∃ K:ℕ,0<K ∧ ∃ zeta:ℝ,0<zeta ∧
    ∃ θ:ℝ,0<θ ∧ ∃ etaEmax:ℝ,0<etaEmax ∧ ∀ etaE:ℝ,0<etaE→etaE≤etaEmax→∃ etaBal:ℝ,0<etaBal ∧ ∃ NI:ℕ,∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
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
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DS
    let E₀':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let E₁':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let tail':=fun e:E₀'=>e.val.1
    let head':=fun e:E₀'=>e.val.2
    let ktail':=fun e:E₁'=>e.val.1
    let khead':=fun e:E₁'=>e.val.2
    ∃ M_D:Finset (MarkedWheel tail' head' ktail' khead' (r+4) π (3*d) (H' false) (H' true)),
      (∀ X∈M_D,∀ Y∈M_D,X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y)) ∧
      (∀ x∉I,(markedPackingRimGraph M_D).degree x≤2*W.card+T.card*(4*(K+4))+2*T.card) ∧
      (∀ x∉I,(Finset.univ.filter (markedPackingSpokes M_D x)).card≤W.card+T.card*(K+4)) ∧
      (∀ u∉W,(Finset.univ.filter (fun x=>markedPackingSpokes M_D x u)).card≤T.card*(r+5)) ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅ ∧
      (M_D.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\W))=∅ ∧
      (∀ X∈M_D,(X.2.val∈W∧markedWheelRows X⊆Iᶜ)∨
        (X.2.val∉J∧∃v∈T,markedWheelRows X⊆insert v Iᶜ∧v∈markedWheelRows X)) ∧
      (∀ a:E₀'⊕E₁',markedStarResource T W
          (Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))→
          Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a)∈M_D.biUnion markedWheelPhysicalResources) ∧
      (∀ x u,H' false x u∨H' true x u→markedStarResource T W (Sum.inr (x,u))→
          Sum.inr (x,u)∈M_D.biUnion markedWheelPhysicalResources) ∧
      ∀ (A B:Type) [Fintype A] [Fintype B] [LinearOrder A] [DecidableEq B],
      ∀ (f:A↪oV) (g:B↪U) (ρA:Equiv.Perm A),(∀ x,f (ρA x)=π (f x))→
      (∀ x,x∈Finset.univ.image f↔x∉T)→(∀ u,u∈Finset.univ.image g↔u∉W)→
      ∀ (XA:Finset A) (ZA:Finset B),(∀ x,f x∈I↔x∈XA)→(∀ u,g u∈J↔u∈ZA)→
      let σA:=rawMarkedRestrictPair f g (rawMarkedDeleteRims σ' (markedPackingRimGraph M_D).edgeFinset)
      let HA:=fun b x u=>markedDeletePhysicalSpokes H' (markedFiniteSpokeGraph (M_D.biUnion markedWheelSpokePairs)) b (f x) (g u)
      let EA₀:=MarkedSampleArc (P.comap f) ρA (3*d) (fun e=>σA (Sum.inl e)) false
      let EA₁:=MarkedSampleArc (P.comap f) ρA (3*d) (fun e=>σA (Sum.inl e)) true
      MarkedOutsideBalance (fun e:EA₀=>e.val.1) (fun e=>e.val.2)
        (fun e:EA₁=>e.val.1) (fun e=>e.val.2) (HA true) Finset.univ
        (Finset.univ.filter (fun z:A×B=>HA false z.1 z.2∨HA true z.1 z.2)) (r+4) XA ZA:=by
  obtain ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,etaEmax,hemax,hall⟩:=
    marked_constructed_deep_active_balance_ordered r hr omega t rho gamma eta ho ht hrho hrho1 hg hg1 hst heta hetaSmall β aLo B pstar hβ hβt haLo hB hpstar
  exact ⟨eps,heps,K,hK,zeta,hzeta,θ,hθ,etaEmax,hemax,
    hall omegaI hIcut deltaI mu hoI hhI hdI hdIs hmu⟩

end Oberwolfach
