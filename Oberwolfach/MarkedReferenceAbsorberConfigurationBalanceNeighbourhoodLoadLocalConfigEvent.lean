module

public import Oberwolfach.MarkedReferenceAbsorberConfigurationBalanceNeighbourhoodLoadLocalEvent
public import Oberwolfach.MarkedRetainedConfigurationsVortex
public import Oberwolfach.MarkedRetainedLocalLoadVortex
public import Oberwolfach.MarkedPackingAdaptiveVortexEvent
public import Oberwolfach.MarkedNeighbourhoodAdaptiveVortexEvent
public import Oberwolfach.MarkedFiniteBalanceAdaptiveVortexEvent
public import Oberwolfach.MarkedCommonAdaptiveVortexEvent
public import Oberwolfach.MarkedSampledReservedTerminalAbsorbers

@[expose] public section

/-! The same retained outcome supplies local configuration counts and local spoke-root loads at every specified level, in addition to the reference estimates, balance, neighbourhood, packing loads, and reserved absorber property. The displayed parent and domain hypotheses remain explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_absorber_configuration_balance_neighbourhood_load_local_config_event
    (k₀ r Q:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω γ tstar kstar κ:ℝ)
    (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀)
    (hγ:0<γ) (hγ1:γ≤1/2) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar) (hκ:0<κ):
    ∃ β βCommon εAbs δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<δAbs ∧ ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,
    ∀ (εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig:ℝ),0<εRef → 0<δRef → 0<η → η<1 → 0<χ →
    0<χCommon → 0<pstar → 0<ζ → 0<εBal → 1≤Kbal → 0<ζBal → 0<χBal → 0<εNbr → 1≤Knbr → 0<ζNbr → 0<χNbr → 0<Bload → 0<εLoad → 1≤Kload → 0<ζLoad → 0<χLoad → 0<ζLocal → 0<χLocal → 0<ζConfig → 0<χConfig →
    ∀ f₀ hNbr d:ℕ,∀ hd:2≤d,∃ M:ℕ,1≤M ∧
    ∀ (V U Γ Color:Type) (W Z Hdom:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)] [∀ i,Fintype (Hdom i)] [∀ i,DecidableEq (Hdom i)],
    M≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ D₀:ℝ,(Fintype.card V:ℝ)/2≤D₀ → D₀≤2*Fintype.card V →
      (∀ v,|(P.degree v:ℝ)-D₀|≤δAbs*Fintype.card V) →
      (∀ v,(1/2+α₀)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (f:∀ i,W i↪oV) (g:∀ i,Z i↪U) (ρi:∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρi i x)=π (f i x)) →
    ∀ L:ℕ,(L+1:ℝ)≤(Fintype.card V:ℝ)^Csize →
      (∀ i≤L,M≤Fintype.card (W i)) → (∀ i≤L,M≤Fintype.card (Z i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,κ*Fintype.card (W i)≤(Fintype.card (Z i):ℝ)) →
      (∀ i≤L,Fintype.card (Z i)≤Fintype.card (W i)) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Kload*Fintype.card (W i)) →
      (∀ i≤L,Fintype.card (Hdom i)≤Fintype.card (W i)) →
    ∀ (A:∀ i,Finset (W i)) (Bset:∀ i,Finset (Z i)) (Scale:ℕ→ℕ),
      (∀ i≤L,M≤(A i).card) → (∀ i≤L,M≤(Bset i).card) →
      (∀ i<L,(Scale (i+1):ℝ)≤η*Scale i) →
      (∀ i≤L,(A i).card≤Scale i) → (∀ i≤L,(Bset i).card≤Scale i) →
      (∀ i≤L,∀ x,ρi i x∈A i ↔ x∈A i) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Kbal*Scale i) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Kbal*Scale i) →
      (∀ i<L,((A (i+1)).card:ℝ)≤η*(A i).card) →
      (∀ i<L,((Bset (i+1)).card:ℝ)≤η*(Bset i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Knbr*(A i).card) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Knbr*(A i).card) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Knbr*(Bset i).card) →
      (∀ i≤L,∀ x:W i,(1/2+γ)*(A i).card≤(((P.comap (f i)).neighborFinset x∩A i).card:ℝ)) →
    ∀ (Dbal:ℕ→ℝ) (δPbal:ℝ),0≤δPbal → δPbal≤εBal/4 →
      (∀ i≤L,∀ x:W i,|(((P.comap (f i)).neighborFinset x∩A i).card:ℝ)-Dbal i|≤δPbal*Scale i) →
    ∀ (D:ℕ→ℝ) (δP:ℝ),0≤δP → δP≤εRef/4 →
      (∀ i≤L,∀ x:W i,|((P.comap (f i)).degree x:ℝ)-D i|≤δP*Fintype.card (W i)) →
      (∀ i≤L,∀ x:W i,(1/2+γ)*Fintype.card (W i)≤((P.comap (f i)).degree x:ℝ)) →
    ∀ (b:∀ i,Hdom i↪Z i) (Dload:ℕ→ℝ) (τ Aload:ℝ)
      (weight:∀ i,(Fin ((r+4)+1)→W i)→ℝ),
      (∀ i≤L,(Fintype.card (W i):ℝ)/2≤Dload i) →
      (∀ i≤L,Dload i≤2*Fintype.card (W i)) →
      (∀ i≤L,SuccessorSequenceWeightConditions (P.comap (f i)) (ρi i) (3*d) (Dload i) τ Aload Bload (weight i)) →
    ∀ (ρ s₀:ℝ) (hρlo:ρstar≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let densities:=marked_seed_density_bounds (r+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let p:=ρ*s₀/2
    let k:=p/((r+4:ℕ):ℝ);
    kstar≤p → kstar≤k → tstar≤s₀/((r+4:ℕ):ℝ) →
    pstar*Fintype.card V≤(s₀/((r+4:ℕ):ℝ))*Fintype.card U →
    (∀ i≤L,p*Dbal i=s₀*(Bset i).card) →
    (∀ i≤L,k*Dbal i=(s₀/((r+4:ℕ):ℝ))*(Bset i).card) →
    (∀ i≤L,(Fintype.card (Hdom i):ℝ)*(s₀/((r+4:ℕ):ℝ))=Dload i*k) →
    (∀ i≤L,(Fintype.card (Hdom i):ℝ)*(s₀/((r+4:ℕ):ℝ))*((r+4:ℕ):ℝ)=Dload i*p) →
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
    1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)-2*χNbr-2*(Fintype.card V:ℝ)^(-Qreal)-χLoad-(Fintype.card V:ℝ)^(-Qreal)-χLocal-(Fintype.card V:ℝ)^(-Qreal)-χConfig-(Fintype.card V:ℝ)^(-Qreal)≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>(((((((∀ i≤L,
        MarkedReferenceConfigurations r (P.comap (f i)) (ρi i) d a j β
          (rawMarkedRestrictPair (f i) (g i) z.1) ∧
        ∀ ζ:ℝ,0≤ζ → 2*ζ≤(3/4)*γ*p^2 → ζ≤γ*min p k/8 →
        ∀ DR:SimpleGraph (W i),(∀ x,(DR.degree x:ℝ)≤ζ*Fintype.card (W i)) →
        MarkedReferenceStatistics (P.comap (f i)) (ρi i) d a j (D i) (εRef+ζ) δRef (γ/2) p k s₀
          (s₀/((r+4:ℕ):ℝ)) (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset) ∧
        MarkedReferenceCutFamilies (P.comap (f i)) (ρi i) d a j (γ/2) p k tstar
          (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)) ∧
        let H:Bool→V→U→Prop:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
        MarkedReservedTerminalAbsorberProperty
          (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false=>e.val.1) (fun e=>e.val.2)
          (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true=>e.val.1) (fun e=>e.val.2)
          (H false) (H true) π (3*d) r size a₀ b₀ e₀ f₀ εAbs) ∧
        (∀ i≤L,∀ δ:ℝ,0≤δ →
          ∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
          (∀ x,(DR.degree x:ℝ)≤δ) → (∀ x,(DS.degree x:ℝ)≤δ) →
          MarkedCommonConfigurationsWithSpokes r (P.comap (f i)) (ρi i) d βCommon (ζ+4*δ/Fintype.card (W i))
            (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
            (markedDeletePhysicalSpokes
              (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
                (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) DS))) ∧
        (∀ i≤L,
          let σi := rawMarkedRestrictPair (f i) (g i) z.1
          let Hi := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)
          let E := MarkedSampleArc (P.comap (f i)) (ρi i) (3*d) (fun e=>σi (Sum.inl e)) false
          let KArc := MarkedSampleArc (P.comap (f i)) (ρi i) (3*d) (fun e=>σi (Sum.inl e)) true
          let S := Finset.univ.filter (fun s:W i×Z i=>Hi false s.1 s.2∨Hi true s.1 s.2)
          let err := (εBal+((r+4)+2:ℕ)*ζBal)*Scale i;
          (∀ v j,|markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S (r+4) (A i) (Bset i) v j|≤err) ∧
          ∀ (KA : Finset (E⊕KArc)) (KS : Finset (W i×Z i)),KS⊆S→
          let R := markedFiniteResources (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρi i) KA KS;
          R.filter (markedInnerResource (A i) (Bset i))=∅→
          ∀ δ:ℝ,0≤δ→
          (∀ physical v,(((markedIncidentEdges (fun e:E=>e.val.1) (fun e=>e.val.2)
            (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρi i) (Hi false) (Hi true) physical v).filter
            (fun e=>markedActivePhysical (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (ρi i) (Hi false) (Hi true) e∈
                R.filter (markedStarResource (A i) (Bset i)))).card:ℝ)≤δ)→
          let σ' := rawMarkedDeleteRims σi (markedSampleArcSetGraph (P.comap (f i)) (ρi i) d σi KA).edgeFinset
          let H' := markedDeletePhysicalSpokes Hi (markedFiniteSpokeGraph KS)
          let E' := MarkedSampleArc (P.comap (f i)) (ρi i) (3*d) (fun e=>σ' (Sum.inl e)) false
          let K' := MarkedSampleArc (P.comap (f i)) (ρi i) (3*d) (fun e=>σ' (Sum.inl e)) true
          let S' := Finset.univ.filter (fun s:W i×Z i=>H' false s.1 s.2∨H' true s.1 s.2);
          (∀ v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
            (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' (r+4) (A i) (Bset i) v j|≤err+((r+4)+2)*δ) ∧
          (∀ v,Sum.elim (fun x=>x∈A i) (fun u=>u∈Bset i) v→∀ j,
            markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
              (fun e:K'=>e.val.1) (fun e=>e.val.2) (H' true) Finset.univ S' (r+4) (A i) (Bset i) v j=
            markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S (r+4) (A i) (Bset i) v j))) ∧
        (∀ i≤L,
          let ω := rawMarkedRestrictPair (f i) (g i) z.1
          let H := fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u);
          ∀ deltaR deltaV deltaU : ℝ,0≤deltaR→0≤deltaV→0≤deltaU→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
            (∀ x,((DR.neighborFinset x∩A i).card:ℝ)≤deltaR)→
            (∀ x,(((Bset i).filter (fun u=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaV)→
            (∀ u,(((A i).filter (fun x=>DS.Adj (Sum.inl x) (Sum.inr u))).card:ℝ)≤deltaU)→
          MarkedRowsWithSpokes (P.comap (f i)) (ρi i) d hNbr (A i) p k
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((εNbr+hNbr*ζNbr)*(A i).card+hNbr*(deltaR+deltaU))
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS) ∧
          MarkedIndicesWithSpokes (ρi i) d hNbr (Bset i)
            (fun u=>q (g i u)) (fun u=>s (g i u)) a j
            ((εNbr+hNbr*ζNbr)*(Bset i).card+hNbr*deltaV)
            (rawMarkedDeleteRims ω DR.edgeFinset) (markedDeletePhysicalSpokes H DS))) ∧
        (∀ i≤L,∀ δ : ℝ,0≤δ→
          ∀ (DR : SimpleGraph (W i)) (DS : SimpleGraph (W i⊕Z i)),
          (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
          MarkedPackingLoadsWithSpokes (P.comap (f i)) (ρi i) d (r+4) (Dload i) p k s₀ (weight i) a j
            (b i) (fun z=>q (g i z)) (fun z=>s (g i z))
            (τ+εLoad+11*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*Kload*ζLoad+
              33*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δ/Fintype.card (W i))
            (rawMarkedDeleteRims (rawMarkedRestrictPair (f i) (g i) z.1) DR.edgeFinset)
            (markedDeletePhysicalSpokes
              (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
                (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a))
                  z.2 a j b (f i x) (g i u)) DS))) ∧
        (∀ i≤L,MarkedLocalSpokeLoadsWithSpokes (P.comap (f i)) (ρi i) d (r+4) (Dload i) p k s₀ (weight i)
          (τ+εLoad+5*(((r+4):ℝ)+1)^4*(2*Bload/(ρstar*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*Kload*ζLocal)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)))) ∧
        (∀ i≤L,MarkedLocalConfigurationsWithSpokes r (P.comap (f i)) (ρi i) d (A i)
          (markedLocalCycleCoefficient r γ (tstar/2) kstar-(r+5:ℕ)*ζConfig)
          (markedLocalPathCoefficient r γ (tstar/2) kstar-(r+4:ℕ)*ζConfig)
          (rawMarkedRestrictPair (f i) (g i) z.1)
          (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
            (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)))) := by
  obtain ⟨β,βCommon,εAbs,δAbs,hβ,hβCommon,hεAbs,hδAbs,hjoint⟩:=
    marked_reference_absorber_configuration_balance_neighbourhood_load_local_event k₀ r Q hr hlen α₀ ρstar sstar ω γ tstar kstar κ
      hα₀ hρstar hsstar hω hmargin hγ hγ1 htstar htstar1 horder hkstar hκ
  refine ⟨β,βCommon,εAbs,δAbs,hβ,hβCommon,hεAbs,hδAbs,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hjoint⟩:=hjoint size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig
    hε hδ hη hη1 hχ hχC hpstar hζ hεBal hKbal hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad hKload hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig f₀ hNbr d hd
  obtain ⟨MJoint,hMJ,hjoint⟩:=hjoint εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal
    hε hδ hη hη1 hχ hχC hpstar hζ hεBal hKbal hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad hKload hζLoad hχLoad hζLocal hχLocal f₀ hNbr d hd
  obtain ⟨MConfig,NConfig,hMC,hNC,hconfig⟩:=marked_retained_configurations_vortex_event r (by omega)
    γ tstar kstar Knbr η χConfig Csize Qreal pstar ζConfig hγ hγ1 htstar hkstar hKnbr hη hη1 hχConfig hpstar hζConfig d hd
  refine ⟨max MJoint (max MConfig NConfig),by omega,?_⟩
  intro V U Γ Color W Z Hdom _ _ _ _ _ _ _ _ _ _ _ _ _ hn hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize hnlevels hnZ hstep hZlo hZhi hZW hHW
    A Bset Scale hA hB hScale hAS hBS hInv hWS hZS hstepA hstepB hWA hZA hWB hPdomain
    Dbal δPbal hδbal hδbalε hPbal D δP hδP hδPε hPreg hPmin
    b Dload τ Aload weight hDloadlo hDloadhi hw ρ s₀ hρlo hρhi hslo hshi densities p k
    hpstar0 hkstar0 htstar0 hmass hDp hDk hLk hLp q hq hQ s hs hS a j hq₀ hs₀
  let μ:=rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hJ:=hjoint V U Γ Color W Z Hdom (by omega) hUlo hUhi P π hπ D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize
    (fun i hi=>by have hh:=hnlevels i hi;omega) (fun i hi=>by have hh:=hnZ i hi;omega) hstep hZlo hZhi hZW hHW
    A Bset Scale (fun i hi=>by have hh:=hA i hi;omega) (fun i hi=>by have hh:=hB i hi;omega)
    hScale hAS hBS hInv hWS hZS hstepA hstepB hWA hZA hWB Dbal δPbal hδbal hδbalε hPbal D δP hδP hδPε hPreg hPmin
    b Dload τ Aload weight hDloadlo hDloadhi hw ρ s₀ hρlo hρhi hslo hshi hpstar0 hkstar0 htstar0 hmass hDp hDk hLk hLp q hq hQ s hs hS a j hq₀ hs₀
  have hC:=hconfig V U Γ Color W Z (by omega) hUhi P π hπ f g ρi hcomm A L hLsize
    (fun i hi=>by have hh:=hA i hi;omega) (fun i hi=>by have hh:=hnZ i hi;omega)
    hstepA hWA hZA hInv hPdomain p k (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 hpstar0 hkstar0
    q hq hQ s hs hS a j s₀ (s₀/((r+4:ℕ):ℝ)) hq₀ hs₀ (horder.trans hslo) htstar0 hmass
  apply (show 1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)-2*χNbr-2*(Fintype.card V:ℝ)^(-Qreal)-χLoad-(Fintype.card V:ℝ)^(-Qreal)-χLocal-(Fintype.card V:ℝ)^(-Qreal)-χConfig-(Fintype.card V:ℝ)^(-Qreal)≤
    μ.probability _-(χConfig+(Fintype.card V:ℝ)^(-Qreal)) by linarith only [hJ]).trans
  apply finiteLaw_good_intersection μ _ _ _
  simp only [Nat.cast_add, Nat.cast_ofNat] at hC ⊢
  linarith only [hC]

end Oberwolfach
