module

public import Oberwolfach.MarkedReferenceAbsorberConfigurationSeparate
public import Oberwolfach.MarkedFiniteBalanceAdaptiveVortexEvent
public import Oberwolfach.MarkedCommonAdaptiveVortexEvent
public import Oberwolfach.MarkedSampledReservedTerminalAbsorbers

@[expose] public section

/-! The original retained experiment simultaneously supplies the fixed
reference estimates at all vortex levels and the reserved terminal
absorber property. The reference conclusion remains uniform over later
bounded deletions, which may depend on the entire retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_reference_absorber_configuration_balance_event_separate_thresholds
    (k₀ r Q:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω γ tstar kstar κ:ℝ)
    (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀)
    (hγ:0<γ) (hγ1:γ≤1/2) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar) (hκ:0<κ):
    ∃ β βCommon εAbs δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<δAbs ∧
    ∀ (εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal:ℝ),0<εRef → 0<δRef → 0<η → η<1 → 0<χ →
    0<χCommon → 0<pstar → 0<ζ → 0<εBal → 1≤Kbal → 0<ζBal → 0<χBal →
    ∀ d:ℕ,∀ hd:2≤d,∃ MLevel:ℕ,1≤MLevel ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ MHost:ℕ,1≤MHost ∧
    ∀ (V U Γ Color:Type) (W Z:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)],
    MHost≤Fintype.card V → ω*Fintype.card V≤(Fintype.card U:ℝ) → Fintype.card U≤Fintype.card V →
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
      (∀ x l,0<l → l<2*d+1 → (π^l) x≠x) →
    ∀ D₀:ℝ,(Fintype.card V:ℝ)/2≤D₀ → D₀≤2*Fintype.card V →
      (∀ v,|(P.degree v:ℝ)-D₀|≤δAbs*Fintype.card V) →
      (∀ v,(1/2+α₀)*Fintype.card V≤(P.degree v:ℝ)) →
    ∀ (f:∀ i,W i↪oV) (g:∀ i,Z i↪U) (ρi:∀ i,Equiv.Perm (W i)),
      (∀ i x,f i (ρi i x)=π (f i x)) →
    ∀ L:ℕ,(L+1:ℝ)≤(Fintype.card V:ℝ)^Csize →
      (∀ i≤L,MLevel≤Fintype.card (W i)) → (∀ i≤L,MLevel≤Fintype.card (Z i)) →
      (∀ i<L,(Fintype.card (W (i+1)):ℝ)≤η*Fintype.card (W i)) →
      (∀ i≤L,κ*Fintype.card (W i)≤(Fintype.card (Z i):ℝ)) →
      (∀ i≤L,Fintype.card (Z i)≤Fintype.card (W i)) →
    ∀ (A:∀ i,Finset (W i)) (Bset:∀ i,Finset (Z i)) (Scale:ℕ→ℕ),
      (∀ i≤L,MLevel≤(A i).card) → (∀ i≤L,MLevel≤(Bset i).card) →
      (∀ i<L,(Scale (i+1):ℝ)≤η*Scale i) →
      (∀ i≤L,(A i).card≤Scale i) → (∀ i≤L,(Bset i).card≤Scale i) →
      (∀ i≤L,∀ x,ρi i x∈A i ↔ x∈A i) →
      (∀ i≤L,(Fintype.card (W i):ℝ)≤Kbal*Scale i) →
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Kbal*Scale i) →
    ∀ (Dbal:ℕ→ℝ) (δPbal:ℝ),0≤δPbal → δPbal≤εBal/4 →
      (∀ i≤L,∀ x:W i,|(((P.comap (f i)).neighborFinset x∩A i).card:ℝ)-Dbal i|≤δPbal*Scale i) →
    ∀ (D:ℕ→ℝ) (δP:ℝ),0≤δP → δP≤εRef/4 →
      (∀ i≤L,∀ x:W i,|((P.comap (f i)).degree x:ℝ)-D i|≤δP*Fintype.card (W i)) →
      (∀ i≤L,∀ x:W i,(1/2+γ)*Fintype.card (W i)≤((P.comap (f i)).degree x:ℝ)) →
    ∀ (ρ s₀:ℝ) (hρlo:ρstar≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let densities:=marked_seed_density_bounds (r+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let p:=ρ*s₀/2
    let k:=p/((r+4:ℕ):ℝ);
    kstar≤p → kstar≤k → tstar≤s₀/((r+4:ℕ):ℝ) →
    pstar*Fintype.card V≤(s₀/((r+4:ℕ):ℝ))*Fintype.card U →
    (∀ i≤L,p*Dbal i=s₀*(Bset i).card) →
    (∀ i≤L,k*Dbal i=(s₀/((r+4:ℕ):ℝ))*(Bset i).card) →
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
    1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>(((∀ i≤L,
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
              (fun e:KArc=>e.val.1) (fun e=>e.val.2) (Hi true) Finset.univ S (r+4) (A i) (Bset i) v j))) := by
  obtain ⟨β,βCommon,εAbs,δAbs,hβ,hβCommon,hεAbs,hδAbs,hjoint⟩:=
    marked_reference_absorber_configuration_common_event_separate_thresholds k₀ r Q hr hlen α₀ ρstar sstar ω γ tstar kstar κ
      hα₀ hρstar hsstar hω hmargin hγ hγ1 htstar htstar1 horder hkstar hκ
  refine ⟨β,βCommon,εAbs,δAbs,hβ,hβCommon,hεAbs,hδAbs,?_⟩
  intro εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal
    hε hδ hη hη1 hχ hχC hpstar hζ hεBal hKbal hζBal hχBal d hd
  obtain ⟨MJoint,hMJ,hjoint⟩:=hjoint εRef δRef η χ χCommon Csize Qreal pstar ζ hε hδ hη hη1 hχ hχC hpstar hζ d hd
  obtain ⟨MBal,NBal,hMB,hNB,hbal⟩:=marked_finite_balance_adaptive_vortex_event (r+4) d hd
    εBal Kbal η χBal Csize Qreal pstar ζBal hεBal hKbal hη hη1 hχBal hpstar hζBal
  refine ⟨max MJoint MBal,by omega,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hjoint⟩:=hjoint size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨MAbs,hMAbs,hjoint⟩:=hjoint f₀
  refine ⟨max MAbs NBal,by omega,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize hnlevels hnZ hstep hZlo hZhi
    A Bset Scale hA hB hScale hAS hBS hInv hWS hZS Dbal δPbal hδbal hδbalε hPbal
    D δP hδP hδPε hPreg hPmin ρ s₀ hρlo hρhi hslo hshi densities p k
    hpstar0 hkstar0 htstar0 hmass hDp hDk q hq hQ s hs hS a j hq₀ hs₀
  let μ:=rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hJ:=hjoint V U Γ Color W Z ((le_max_left _ _).trans hn) hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize
    (fun i hi=>(le_max_left _ _).trans (hnlevels i hi)) (fun i hi=>(le_max_left _ _).trans (hnZ i hi))
    hstep hZlo hZhi D δP hδP hδPε hPreg hPmin
    ρ s₀ hρlo hρhi hslo hshi hpstar0 hkstar0 htstar0 hmass q hq hQ s hs hS a j hq₀ hs₀
  have hB:=hbal V U Γ Color W Z (by omega) hUhi P π hπ f g ρi hcomm A Bset Scale L hLsize
    (fun i hi=>by have hh:=hA i hi;omega) (fun i hi=>by have hh:=hB i hi;omega)
    hScale hAS hBS hInv hWS hZS Dbal δPbal hδbal hδbalε hPbal
    p k (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le
    densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS a j s₀ (s₀/((r+4:ℕ):ℝ)) hq₀ hs₀ hDp hDk
    (by field_simp) hmass
  apply (show 1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)≤
    μ.probability _-(χBal+(Fintype.card V:ℝ)^(-Qreal)) by linarith only [hJ]).trans
  apply finiteLaw_good_intersection μ _ _ _
  simp only [Nat.cast_add, Nat.cast_ofNat] at hB ⊢
  linarith only [hB]

end Oberwolfach
