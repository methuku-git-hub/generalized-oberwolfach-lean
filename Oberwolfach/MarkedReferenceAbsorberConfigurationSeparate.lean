module

public import Oberwolfach.MarkedReferenceAbsorberCommonSeparate
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

theorem marked_reference_absorber_configuration_common_event_separate_thresholds
    (k₀ r Q:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω γ tstar kstar κ:ℝ)
    (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀)
    (hγ:0<γ) (hγ1:γ≤1/2) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar) (hκ:0<κ):
    ∃ β βCommon εAbs δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<δAbs ∧
    ∀ (εRef δRef η χ χCommon Csize Qreal pstar ζ:ℝ),0<εRef → 0<δRef → 0<η → η<1 → 0<χ →
    0<χCommon → 0<pstar → 0<ζ →
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
    ∀ (D:ℕ→ℝ) (δP:ℝ),0≤δP → δP≤εRef/4 →
      (∀ i≤L,∀ x:W i,|((P.comap (f i)).degree x:ℝ)-D i|≤δP*Fintype.card (W i)) →
      (∀ i≤L,∀ x:W i,(1/2+γ)*Fintype.card (W i)≤((P.comap (f i)).degree x:ℝ)) →
    ∀ (ρ s₀:ℝ) (hρlo:ρstar≤ρ) (hρhi:ρ≤1) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let densities:=marked_seed_density_bounds (r+4) (by omega) ρ s₀ ρstar sstar hρstar hsstar hρlo hρhi hslo hshi
    let p:=ρ*s₀/2
    let k:=p/((r+4:ℕ):ℝ);
    kstar≤p → kstar≤k → tstar≤s₀/((r+4:ℕ):ℝ) →
    pstar*Fintype.card V≤(s₀/((r+4:ℕ):ℝ))*Fintype.card U →
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ)) → (∀ u,s u j=s₀) →
    1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (fun z=>((∀ i≤L,
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
                (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u)) DS))) := by
  obtain ⟨βCommon,hβCommon,hcommon⟩:=marked_common_adaptive_vortex_event r (by omega) γ sstar tstar kstar κ
    hγ hγ1 hsstar htstar hkstar hκ
  obtain ⟨β,εAbs,δAbs,hβ,hεAbs,hδAbs,hjoint⟩:=marked_reference_absorber_common_event_separate_thresholds
    k₀ r Q hr hlen α₀ ρstar sstar ω γ tstar kstar κ hα₀ hρstar hsstar hω hmargin
    hγ hγ1 htstar htstar1 horder hkstar hκ
  refine ⟨β,βCommon,εAbs,δAbs,hβ,hβCommon,hεAbs,hδAbs,?_⟩
  intro εRef δRef η χ χCommon Csize Qreal pstar ζ hε hδ hη hη1 hχ hχC hpstar hζ d hd
  obtain ⟨MRef,hMRef,hjoint⟩:=hjoint εRef δRef η χ hε hδ hη hη1 hχ d hd
  obtain ⟨MCommon,NCommon,hMC,hNC,hcommon⟩:=hcommon η χCommon Csize Qreal pstar ζ hη hη1 hχC hpstar hζ d hd
  refine ⟨max MRef MCommon,by omega,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hjoint⟩:=hjoint size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨MAbs,hMAbs,hjoint⟩:=hjoint f₀
  refine ⟨max MAbs NCommon,by omega,?_⟩
  intro V U Γ Color W Z _ _ _ _ _ _ _ _ _ _ _ hn hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize hnlevels hnZ hstep hZlo hZhi D δP hδP hδPε hPreg hPmin
    ρ s₀ hρlo hρhi hslo hshi densities p k hpstar0 hkstar0 htstar0 hmass q hq hQ s hs hS a j hq₀ hs₀
  let μ:=rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hJ:=hjoint V U Γ Color W Z ((le_max_left _ _).trans hn) hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L
    (fun i hi=>(le_max_left _ _).trans (hnlevels i hi)) hstep hZlo hZhi D δP hδP hδPε hPreg hPmin
    ρ s₀ hρlo hρhi hslo hshi hpstar0 hkstar0 htstar0 q hq hQ s hs hS a j hq₀ hs₀
  have hC:=hcommon V U Γ Color W Z (by omega) hUhi P π hπ f g ρi hcomm L hLsize
    (fun i hi=>by have hh:=hnlevels i hi;omega) (fun i hi=>by have hh:=hnZ i hi;omega)
    hstep hZlo hZhi hPmin p k (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le
    densities.2.2.2.2.2.2.2.2 hpstar0 hkstar0 q hq hQ s hs hS a j s₀ (s₀/((r+4:ℕ):ℝ)) hq₀ hs₀ hslo htstar0 hmass
  apply (show 1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)≤
    μ.probability _-(χCommon+(Fintype.card V:ℝ)^(-Qreal)) by linarith only [hJ]).trans
  apply finiteLaw_good_intersection μ _ _ _
  linarith only [hC]

end Oberwolfach
