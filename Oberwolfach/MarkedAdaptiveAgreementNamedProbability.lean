module

public import Oberwolfach.MarkedReferenceAdaptiveAbsorberAgreementSeparate
public import Oberwolfach.MarkedAdaptiveFailureBudget
public import Oberwolfach.MarkedAdaptiveAgreementProperty

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_adaptive_agreement_named_probability_uniform
    (k₀ r Q:ℕ) (hQpow:0<Q) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α₀ ρstar sstar ω γ tstar kstar κ:ℝ)
    (hα₀:0<α₀) (hρstar:0<ρstar) (hsstar:0<sstar) (hω:0<ω)
    (hmargin:successorCycleRatio k₀+α₀/2≤1/2+α₀)
    (hγ:0<γ) (hγ1:γ≤1/2) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar) (hκ:0<κ):
    ∃ β βCommon εAbs εRob ζRob δAbs:ℝ,0<β∧0<βCommon∧0<εAbs∧0<εRob∧0<ζRob∧0<δAbs ∧
    ∀ (εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig:ℝ),0<εRef → 0<δRef → 0<η → η<1 → 0<χ →
    0<χCommon → 0<pstar → 0<ζ → 0<εBal → 1≤Kbal → 0<ζBal → 0<χBal → 0<εNbr → 1≤Knbr → 0<ζNbr → 0<χNbr → 0<Bload → 0<εLoad → 1≤Kload → 0<ζLoad → 0<χLoad → 0<ζLocal → 0<χLocal → 0<ζConfig → 0<χConfig →
    ∀ ε₀:ℝ,0<Qreal → χ+χCommon+χBal+2*χNbr+χLoad+χLocal+χConfig<ε₀ →
    ∀ hNbr d:ℕ,∀ hd:2≤d,∃ MLevel:ℕ,1≤MLevel ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀ aRob bRob eRob:ℕ,∀ f₀:ℕ,∃ MHost:ℕ,1≤MHost ∧
    ∀ (V U Γ Color:Type) (W Z Hdom:ℕ→Type)
      [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color] [LinearOrder V] [Nonempty V] [DecidableEq U]
      [∀ i,Fintype (W i)] [∀ i,Fintype (Z i)] [∀ i,LinearOrder (W i)] [∀ i,DecidableEq (Z i)] [∀ i,Fintype (Hdom i)] [∀ i,DecidableEq (Hdom i)],
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
      (∀ i≤L,(Fintype.card (Z i):ℝ)≤Kload*Fintype.card (W i)) →
      (∀ i≤L,Fintype.card (Hdom i)≤Fintype.card (W i)) →
    ∀ (A:∀ i,Finset (W i)) (Bset:∀ i,Finset (Z i)) (Scale:ℕ→ℕ),
      (∀ i≤L,MLevel≤(A i).card) → (∀ i≤L,MLevel≤(Bset i).card) →
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
    1-ε₀≤
      (rawMarkedRetentionLaw π d hd a p k (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).probability
      (MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζRob εRef δRef γ p k s₀ tstar ζ εBal ζBal εNbr ζNbr Bload εLoad Kload ζLoad ζLocal ζConfig ρstar sstar kstar τ
        P π f g ρi A Bset Scale D Dload b weight q s a j) := by
  obtain ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,hcore⟩:=
    marked_reference_adaptive_absorber_agreement_joint_event_separate_thresholds k₀ r Q hr hlen
      α₀ ρstar sstar ω γ tstar kstar κ hα₀ hρstar hsstar hω hmargin hγ hγ1 htstar htstar1 horder hkstar hκ
  refine ⟨β,βCommon,εAbs,εRob,ζRob,δAbs,hβ,hβCommon,hεAbs,hεRob,hζRob,hδAbs,?_⟩
  intro εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig
    hε hδ hη hη1 hχ hχC hpstar hζ hεBal hKbal hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad hKload hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig ε₀ hQreal hgap hNbr d hd
  obtain ⟨MLevel,hML,hcore⟩:=hcore εRef δRef η χ χCommon Csize Qreal pstar ζ εBal Kbal ζBal χBal εNbr Knbr ζNbr χNbr Bload εLoad Kload ζLoad χLoad ζLocal χLocal ζConfig χConfig
    hε hδ hη hη1 hχ hχC hpstar hζ hεBal hKbal hζBal hχBal hεNbr hKnbr hζNbr hχNbr hBload hεLoad hKload hζLoad hχLoad hζLocal hχLocal hζConfig hχConfig hNbr d hd
  refine ⟨MLevel,hML,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,aRob,bRob,eRob,hcore⟩:=hcore size
  refine ⟨a₀,b₀,e₀,aRob,bRob,eRob,?_⟩
  intro f₀
  obtain ⟨MHost,hMH,hcore⟩:=hcore f₀
  obtain ⟨N,hN⟩:=eventually_marked_adaptive_agreement_failure_below χ χCommon χBal χNbr χLoad χLocal χConfig Qreal ε₀ Q hQreal hQpow hgap
  refine ⟨max MHost N,by omega,?_⟩
  intro V U Γ Color W Z Hdom _ _ _ _ _ _ _ _ _ _ _ _ _ hn hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize hnlevels hnZ hstep hZlo hZhi hZW hHW
    A Bset Scale hA hB hScale hAS hBS hInv hWS hZS hstepA hstepB hWA hZA hWB hPdomain
    Dbal δPbal hδbal hδbalε hPbal D δP hδP hδPε hPreg hPmin
    b Dload τ Aload weight hDloadlo hDloadhi hw ρ s₀ hρlo hρhi hslo hshi densities p k
    hpstar0 hkstar0 htstar0 hmass hDp hDk hLk hLp q hq hQ s hs hS a j hq₀ hs₀
  have hj:=hcore V U Γ Color W Z Hdom (by omega) hUlo hUhi P π hπ
    D₀ hDlo hDhi hnear hmind f g ρi hcomm L hLsize
    hnlevels hnZ hstep hZlo hZhi hZW hHW A Bset Scale hA hB
    hScale hAS hBS hInv hWS hZS hstepA hstepB hWA hZA hWB hPdomain
    Dbal δPbal hδbal hδbalε hPbal D δP hδP hδPε hPreg hPmin
    b Dload τ Aload weight hDloadlo hDloadhi hw ρ s₀ hρlo hρhi hslo hshi
    hpstar0 hkstar0 htstar0 hmass hDp hDk hLk hLp q hq hQ s hs hS a j hq₀ hs₀
  have hb:=hN (Fintype.card V) (by omega)
  have hbound:1-ε₀ ≤ 1-χ-2/(Fintype.card V:ℝ)^Q-χCommon-(Fintype.card V:ℝ)^(-Qreal)-χBal-(Fintype.card V:ℝ)^(-Qreal)-2*χNbr-2*(Fintype.card V:ℝ)^(-Qreal)-χLoad-(Fintype.card V:ℝ)^(-Qreal)-χLocal-(Fintype.card V:ℝ)^(-Qreal)-χConfig-(Fintype.card V:ℝ)^(-Qreal)-2/(Fintype.card V:ℝ)^Q-1/(Fintype.card V:ℝ)^Q:=by
    simp only [div_eq_mul_inv] at hb ⊢
    linarith only [hb]
  exact hbound.trans hj
end Oberwolfach
