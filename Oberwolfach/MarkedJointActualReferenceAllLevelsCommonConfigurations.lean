module

public import Oberwolfach.MarkedJointActualReferenceActiveParentLoad
public import Oberwolfach.MarkedActualJointBalanceWitness
public import Oberwolfach.MarkedActualInnerBalanceWitness
public import Oberwolfach.MarkedBalanceReferenceEventBudget
public import Oberwolfach.MarkedActualInnerCutEvent
public import Oberwolfach.MarkedActualParentConfigurationEvent
public import Oberwolfach.MarkedActualParentCommonConfigurationEvent

@[expose] public section
/-! Reference, absorber, load and both balance estimates on one retained outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_joint_actual_reference_all_levels_common_configurations_witness
    (r h k₀:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρ₀ sstar tstar kstar tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2)
    (htolRef:0<tolRef) (hpstarRef:0<pstarRef)
    (hpstarRefBound:pstarRef≤ρ₀*tstar/4) (hζActive:0<ζActive)
    (hτ:0<τ) (htolLocal:0<tolLocal) (hζLocal:0<ζLocal)
    (hτParent:0<τParent) (htolParent:0<tolParent) (hζParent:0<ζParent) (hepsBal:0<epsBal) (hζBal:0<ζBal) (hζCut:0<ζCut) (hζCfg:0<ζCfg):
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig βCommon βmax:ℝ,0<βconfig ∧ 0<βCommon ∧ 0<βmax ∧
    ∀ ζCommon:ℝ,0<ζCommon→∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,
    ∀ εref δref β ε:ℝ,
    0<εref→0<δref→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ (f₀ d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    m₀≤m→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
      (hpres:∀ i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i),
    (∀ x l,0<l→l<2*d+1→(π^l) x≠x)→∀ L:ℕ,L<Q.length→
    letI : Nonempty V:=Fintype.card_pos_iff.mp hn
    let W:=fun i=>markedVortexVertexType Q i
    let Z:=fun i=>markedVortexHubType Q i
    let A:∀ i,Finset (W i):=fun i=>Finset.univ\markedVortexInnerVertices Q i
    let B:∀ i,Finset (Z i):=fun i=>Finset.univ\markedVortexInnerHubs Q i
    let X:=fun i=>↥(A i)
    let f:=fun i=>markedVortexActiveVertexEmbedding Q i
    let g:=fun i=>markedVortexActiveHubEmbedding Q i
    let ρ:=fun i=>markedVortexActivePermutation Q π hpres i
    let Dactive:=fun i=>2*((B i).card:ℝ)/initialIndexDensity U D
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let fParent:=markedVortexVertexEmbedding Q
    let gParent:=markedVortexHubEmbedding Q
    let ρParent:=markedVortexPermutation Q π hpres
    let Dparent:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    ∃ weightParent:∀ i,(Fin (r+4+1)→W i)→ℝ,
    ∃ weight:∀ i,(Fin (r+4+1)→X i)→ℝ,
    ∀ (Γ Color:Type) [Fintype Γ] [Fintype Color] (s₀:ℝ) (hslo:sstar≤s₀) (hshi:s₀≤1/100),
    let dens:=initialIndexDensity U D
    let densities:=marked_seed_density_bounds (r+4) (by omega) dens s₀ ρ₀ sstar hρ₀ hsstar hρlo hρhi hslo hshi
    let p:=dens*s₀/2
    let kval:=p/((r+4:ℕ):ℝ);
    kstar≤p→kstar≤kval→
    ∀ (q:U→Γ→ℝ) (hq:∀ u a,0≤q u a) (hQ:∀ u,∑ a,q u a≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a)) (a:Γ) (j:Color),
      (∀ u,q u a=s₀/((r+4:ℕ):ℝ))→(∀ u,s u j=s₀)→tstar≤s₀/((r+4:ℕ):ℝ)→
    let Eref:=MarkedReferenceActiveAbsorberProperty r h d (α/2) βconfig εref δref tolRef ζActive ζAbs tstar εAbs
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j
    let EParent:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>
      (∀ i≤L,∀ δ:ℝ,0≤δ→∀ (DR:SimpleGraph (W i)) (DS:SimpleGraph (W i⊕Z i)),
        (∀ x,(DR.degree x:ℝ)≤δ)→(∀ x,(DS.degree x:ℝ)≤δ)→
        MarkedPackingLoadsWithSpokes (G.comap (fParent i)) (ρParent i) d (r+4) (Dparent i) p kval s₀ (weightParent i) a j
          (Function.Embedding.refl (Z i)) (fun u=>q (gParent i u)) (fun u=>s (gParent i u))
          (τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent+
            33*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*δ/Fintype.card (W i))
          (rawMarkedDeleteRims (rawMarkedRestrictPair (fParent i) (gParent i) z.1) DR.edgeFinset)
          (markedDeletePhysicalSpokes
            (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
              (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u)) DS)) ∧
        (∀ i≤L+1,MarkedLocalSpokeLoadsWithSpokes (G.comap (f i)) (ρ i) d (r+4) (Dactive i) p kval s₀ (weight i)
        (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζLocal)
        (rawMarkedRestrictPair (f i) (g i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f i x) (g i u))) ∧ Eref z;
    let fCut:=fun i=>markedVortexVertexEmbedding Q (i+1)
    let gCut:=fun i=>markedVortexHubEmbedding Q (i+1)
    let ρCut:=fun i=>markedVortexPermutation Q π hpres (i+1)
    let ECut:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedCutFamiliesWithSpokes (G.comap (fCut i)) (ρCut i) d (α/2) p kval tstar ζCut
        (rawMarkedRestrictPair (fCut i) (gCut i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fCut i x) (gCut i u));
    let EConfig:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (G.comap (fParent i)) (ρParent i) d Finset.univ
        (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
        (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    let ECommon:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedCommonConfigurationsWithSpokes r (G.comap (fParent i)) (ρParent i) d βCommon ζCommon
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    ∃ z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a,
      0<(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).mass z ∧
      MarkedActualVortexBalanceProperty Q π hpres d (r+4) L a j epsBal ζBal
        (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z ∧
      (L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) a j epsBal ζBal
        (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z  :=by
  obtain ⟨βCommon,βcommon,hβCommon,hβcommon,hcommon⟩:=marked_actual_parent_common_configuration_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num)
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βparent,hβconfig,hβparent,hparent⟩:=
    marked_joint_actual_reference_active_parent_load r h k₀ 1 hr hlen α ρ₀ sstar tstar kstar
      tolRef (1/100) 1 pstarRef ζActive τ tolLocal (1/100) 1 ζLocal τParent tolParent (1/100) 1 ζParent
      hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin htolRef (by norm_num)
      hpstarRef hpstarRefBound hζActive hτ htolLocal (by norm_num) hζLocal hτParent htolParent (by norm_num) hζParent
  obtain ⟨βbalance,hβbalance,hbalance⟩:=marked_actual_joint_balance_witness (r+4) (by omega) α ρ₀ sstar tstar epsBal ζBal
    hα hρ₀ hsstar htstar hepsBal hζBal
  obtain ⟨βcut,hβcut,hcut⟩:=marked_actual_inner_cut_event (r+4) (by omega) α ρ₀ sstar tstar kstar (1/100) 1 ζCut
    hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hζCut
  obtain ⟨βinner,hβinner,hinner⟩:=marked_actual_inner_balance_witness (r+4) (by omega) α ρ₀ sstar tstar epsBal ζBal
    hα hρ₀ hsstar htstar hepsBal hζBal
  obtain ⟨βcfg,hβcfg,hcfg⟩:=marked_actual_parent_configuration_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 ζCfg hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hζCfg
  let βmax:=min βparent (min βbalance (min βcut (min βinner (min βcfg βcommon))))
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βCommon,βmax,hβconfig,hβCommon,by dsimp [βmax];positivity,?_⟩
  intro ζCommon hζCommon size
  obtain ⟨a₀,b₀,e₀,hparent⟩:=hparent size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro εref δref β ε hεref hδref hb hbmax hbε he he1 f₀ d hd
  have hbparent:β≤βparent:=hbmax.trans (min_le_left _ _)
  have hbbalance:β≤βbalance:=hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbcut:β≤βcut:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbinner:β≤βinner:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hbcfg:β≤βcfg:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbcommon:β≤βcommon:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))))
  obtain ⟨mParent,hmParent,hparent⟩:=hparent εref δref (1/100) β ε hεref hδref (by norm_num) hb hbparent hbε he he1 f₀ d hd
  obtain ⟨NBalance,hNBalance,mBalance,hmBalance,hbalance⟩:=hbalance ε he he1.le d hd
  obtain ⟨NCut,hNCut,hcut⟩:=hcut d hd
  obtain ⟨mCut,hmCut,hcut⟩:=hcut ε he he1.le
  obtain ⟨NInner,hNInner,mInner,hmInner,hinner⟩:=hinner ε he he1.le d hd
  obtain ⟨NCfg,hNCfg,hcfg⟩:=hcfg d hd
  obtain ⟨mCfg,hmCfg,hcfg⟩:=hcfg ε he he1.le
  obtain ⟨NCommon,hNCommon,hcommon⟩:=hcommon ζCommon hζCommon d hd
  obtain ⟨mCommon,hmCommon,hcommon⟩:=hcommon ε he he1.le
  let m₀:=max mParent (max mBalance (max NBalance (max mCut (max NCut (max mInner (max NInner (max mCfg (max NCfg (max mCommon (max NCommon 200))))))))))
  have hm₀:1≤m₀:=hmParent.trans (le_max_left _ _)
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hmn Q π hpres hshort L hL W Z A B X f g ρ Dactive pstarLocal fParent gParent ρParent Dparent
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hmParent':mParent≤m:=by dsimp [m₀] at hm;omega
  have hmBalance':mBalance≤m:=by dsimp [m₀] at hm;omega
  have hnBalance:NBalance≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmCut':mCut≤m:=by dsimp [m₀] at hm;omega
  have hnCut:NCut≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmInner':mInner≤m:=by dsimp [m₀] at hm;omega
  have hnInner:NInner≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmCfg':mCfg≤m:=by dsimp [m₀] at hm;omega
  have hnCfg:NCfg≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmCommon':mCommon≤m:=by dsimp [m₀] at hm;omega
  have hnCommon:NCommon≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hn200:200≤Fintype.card V:=by dsimp [m₀] at hm;omega
  obtain ⟨weightParent,weight,hparent⟩:=hparent V U G D m hreg hn hD hρlo hρhi hmParent' hmn Q π hpres hshort L hL
  refine ⟨weightParent,weight,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Eref EParent fCut gCut ρCut ECut EConfig ECommon
  let μ:=rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
    (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS
  have hp:=hparent Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hpow:(Fintype.card V:ℝ)^(-(1:ℝ))=1/(Fintype.card V:ℝ):=by
    rw [Real.rpow_neg hnpos.le,Real.rpow_one,one_div]
  have hbound:1-(1/10:ℝ)-5*(Fintype.card V:ℝ)^(-(1:ℝ))-9*(Fintype.card V:ℝ)^(-(1:ℝ))≤μ.probability EParent:=by
    change 1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-((1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+((1/100:ℝ)+2*(1/100:ℝ)+2*(Fintype.card V:ℝ)^(-(1:ℝ))+2/(Fintype.card V:ℝ)^1))≤μ.probability EParent at hp
    rw [hpow] at hp ⊢
    have hnonneg:0≤1/(Fintype.card V:ℝ):=by positivity
    simp only [pow_one] at hp
    have htwo:(2:ℝ)/(Fintype.card V:ℝ)=2*(1/(Fintype.card V:ℝ)):=by ring
    rw [htwo] at hp
    linarith
  let errParent:ℝ:=1/10+5*(Fintype.card V:ℝ)^(-(1:ℝ))+9*(Fintype.card V:ℝ)^(-(1:ℝ))
  have hParentProb:1-errParent≤μ.probability EParent:=by dsimp [errParent];linarith only [hbound]
  have hCutProb:=hcut V U G D m β Q hreg hn hnCut hD hρlo hρhi hb hbcut hmCut' π hpres hshort L hL
    Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo EParent errParent hParentProb
  have hCutProb':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-errParent≤μ.probability (fun z=>ECut z ∧ EParent z):=by exact hCutProb
  let errCut:ℝ:=(1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+errParent
  have hCutBound:1-errCut≤μ.probability (fun z=>ECut z ∧ EParent z):=by dsimp [errCut];linarith only [hCutProb']
  have hCfgProb:=hcfg V U G D m β Q hreg hn hnCfg hD hρlo hρhi hb hbcfg hmCfg' π hpres hshort L hL
    Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>ECut z ∧ EParent z) errCut hCutBound
  have hCfgProb':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-errCut≤μ.probability (fun z=>EConfig z ∧ ECut z ∧ EParent z):=by exact hCfgProb
  let errCfg:ℝ:=(1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+errCut
  have hCfgBound:1-errCfg≤μ.probability (fun z=>EConfig z ∧ ECut z ∧ EParent z):=by dsimp [errCfg];linarith only [hCfgProb']
  have hCommonProb:=hcommon V U G D m β Q hreg hn hnCommon hD hρlo hρhi hb hbcommon hmCommon' π hpres hshort L hL
    Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>EConfig z ∧ ECut z ∧ EParent z) errCfg hCfgBound
  have hCommonProb':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-errCfg≤μ.probability (fun z=>ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by exact hCommonProb
  have hn200r:(200:ℝ)≤Fintype.card V:=by exact_mod_cast hn200
  have hdiv:(17:ℝ)/(Fintype.card V:ℝ)≤17/200:=by apply (div_le_iff₀ hnpos).2;linarith
  have hExtra:(3/4:ℝ)≤μ.probability (fun z=>ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by
    dsimp [errCfg,errCut,errParent] at hCommonProb'
    rw [hpow] at hCommonProb'
    have heq:(17:ℝ)*(1/(Fintype.card V:ℝ))=17/(Fintype.card V:ℝ):=by ring
    rw [←heq] at hdiv
    linarith only [hCommonProb',hdiv]
  by_cases hzero:L=0
  · have hresult:=hinner V U G D m β Q hreg hn hnInner hD hρlo hρhi hb hbinner hmInner' π hpres hshort L hL
      Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) hExtra
    obtain ⟨z,hz,hi,hcommon,hcfg,hc,hp⟩:=hresult
    exact ⟨z,hz,hi,Or.inl hzero,hcommon,hcfg,hc,hp⟩
  · cases L with
    | zero => exact (hzero rfl).elim
    | succ jlevel =>
      have hjlen:jlevel+1<Q.length:=by omega
      have hresult:=hbalance V U G D m β Q hreg hn hnBalance hD hρlo hρhi hb hbbalance hmBalance' π hpres hshort jlevel hjlen
        Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) hExtra
      obtain ⟨z,hz,hi,hd,hcommon,hcfg,hc,hp⟩:=hresult
      refine ⟨z,hz,?_,?_,hcommon,hcfg,hc,hp⟩
      · simpa only [Nat.succ_eq_add_one] using hi
      · right
        simpa using hd
end Oberwolfach
