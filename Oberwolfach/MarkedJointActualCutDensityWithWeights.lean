module

public import Oberwolfach.MarkedActualParentCutsTargetEvent
public import Oberwolfach.MarkedActualParentSpokeAgreementEvent
public import Oberwolfach.MarkedActualParentFullNeighbourhoodEvent
public import Oberwolfach.MarkedActualNextActiveNonDeeperHubsRowsEvent
public import Oberwolfach.MarkedActualNextActiveNonDeeperHubsLoadEvent
public import Oberwolfach.MarkedJointActualReferenceActiveParentLoadOrderedWithWeights
public import Oberwolfach.MarkedActualNextActiveAllParentHubsConfigurationEvent
public import Oberwolfach.MarkedJointActualReferenceActiveParentLoadOrdered
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
theorem marked_joint_actual_reference_all_levels_actual_cut_density_with_weights
    (r h k₀:ℕ) (hr:2≤r) (hlen:r+4+1=(k₀+2)*2)
    (α ρ₀ sstar tstar kstar:ℝ)
    (hα:0<α) (hα1:α≤1) (hρ₀:0<ρ₀) (hsstar:0<sstar) (htstar:0<tstar) (htstar1:tstar≤1)
    (horder:tstar≤sstar) (hkstar:0<kstar)
    (hmargin:successorCycleRatio k₀+α/4≤1/2+α/2)
    :
    ∃ εAbs ζAbs δAbs:ℝ,0<εAbs ∧ 0<ζAbs ∧ 0<δAbs ∧
    ∃ βconfig βCommon:ℝ,0<βconfig ∧ 0<βCommon ∧
    ∀ tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr:ℝ,
    0<tolRef→0<pstarRef→pstarRef≤ρ₀*tstar/4→0<ζActive→
    0<τ→0<tolLocal→0<ζLocal→0<τParent→0<tolParent→0<ζParent→0<epsBal→0<ζBal→0<ζCut→0<ζCfg→0<rowErr→
    ∃ βmax:ℝ,0<βmax ∧ ∀ ζCommon:ℝ,0<ζCommon→∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,
    ∀ εref δref β ε:ℝ,
    0<εref→0<δref→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ ζWide ζRow:ℝ,0<ζWide→0<ζRow→∀ (f₀ d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
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
    let gWide:=markedVortexNonDeeperHubToPhysical Q
    let ρParent:=markedVortexPermutation Q π hpres
    let Dparent:=fun i=>2*(Fintype.card (Z i):ℝ)/initialIndexDensity U D;
    ∃ weightParent:∀ i,(Fin (r+4+1)→W i)→ℝ,
    ∃ weight:∀ i,(Fin (r+4+1)→X i)→ℝ,
    (∀ i≤L,SuccessorSequenceWeightConditions (G.comap (fParent i)) (ρParent i) (3*d)
      (Dparent i) τParent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i)) ∧
    (∀ i≤L+1,SuccessorSequenceWeightConditions (G.comap (f i)) (ρ i) (3*d)
      (Dactive i) τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i)) ∧
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
    let EActive:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedLocalConfigurationsWithSpokes r (G.comap (f (i+1))) (ρ (i+1)) d Finset.univ
        (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
        (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
        (rawMarkedRestrictPair (f (i+1)) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f (i+1) x) (gParent i u));
    let EWide:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedLocalSpokeLoadsWithSpokes (G.comap (f (i+1))) (ρ (i+1)) d (r+4) (Dactive (i+1)) p kval s₀ (weight (i+1))
        (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide)
        (rawMarkedRestrictPair (f (i+1)) (gWide i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f (i+1) x) (gWide i u));
    let ERow:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedRowsWithSpokes (G.comap (f (i+1))) (ρ (i+1)) d 1 Finset.univ p kval
        (fun u=>q (gWide i u)) (fun u=>s (gWide i u)) a j ((rowErr+ζRow)*Fintype.card (X (i+1)))
        (rawMarkedRestrictPair (f (i+1)) (gWide i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f (i+1) x) (gWide i u));
    let ECommon:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedCommonConfigurationsWithSpokes r (G.comap (fParent i)) (ρParent i) d βCommon ζCommon
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    let EFull:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedRowsWithSpokes (G.comap (fParent i)) (ρParent i) d (r+12) Finset.univ p kval
        (fun u=>q (gParent i u)) (fun u=>s (gParent i u)) a j
        ((tolRef+(r+12:ℕ)*ζActive)*Fintype.card (W i))
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u)) ∧
      MarkedIndicesWithSpokes (ρParent i) d (r+12) Finset.univ
        (fun u=>q (gParent i u)) (fun u=>s (gParent i u)) a j
        ((tolRef+(r+12:ℕ)*ζActive)*Fintype.card (Z i))
        (rawMarkedRestrictPair (fParent i) (gParent i) z.1)
        (fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u));
    let EAgreement:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      let ω:=rawMarkedRestrictPair (fParent i) (gParent i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fParent i x) (gParent i u);
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes (ρParent i) d ω a j b x u↔H b x u) then (1:ℝ) else 0)≤ζActive*Fintype.card (Z i)) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes (ρParent i) d ω a j b x u↔H b x u) then (1:ℝ) else 0)≤ζActive*Fintype.card (W i));
    let EActualCuts:=fun z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a=>∀ i≤L,
      MarkedReferenceCutFamilies (G.comap (fParent i)) (ρParent i) d a j (α/8) p kval
        (s₀/((r+4:ℕ):ℝ)) (rawMarkedRestrictPair (fParent i) (gParent i) z.1);
    ∃ z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a,
      0<(rawMarkedRetentionLaw π d hd a p kval (densities.1.trans_le densities.2.1).le
        (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2 q hq hQ s hs hS).mass z ∧
      MarkedActualVortexBalanceProperty Q π hpres d (r+4) L a j epsBal ζBal
        (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) z ∧
      (L=0 ∨ MarkedActualVortexBalanceProperty Q π hpres d (r+4) (L-1) a j epsBal ζBal
        (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) ∧ EActualCuts z ∧ EAgreement z ∧ EFull z ∧ ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z  :=by
  obtain ⟨βCommon,βcommon,hβCommon,hβcommon,hcommon⟩:=marked_actual_parent_common_configuration_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num)
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,hβconfig,hparent⟩:=
    marked_joint_actual_reference_active_parent_load_ordered_with_weights r h k₀ 1 hr hlen α ρ₀ sstar tstar kstar
      hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βCommon,hβconfig,hβCommon,?_⟩
  intro tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr
    htolRef hpstarRef hpstarRefBound hζActive hτ htolLocal hζLocal hτParent htolParent hζParent hepsBal hζBal hζCut hζCfg hrowErr
  obtain ⟨βparent,hβparent,hparent⟩:=hparent
      tolRef (1/100) 1 pstarRef ζActive τ tolLocal (1/100) 1 ζLocal τParent tolParent (1/100) 1 ζParent
      htolRef (by norm_num) hpstarRef hpstarRefBound hζActive hτ htolLocal (by norm_num) hζLocal hτParent htolParent (by norm_num) hζParent
  obtain ⟨βbalance,hβbalance,hbalance⟩:=marked_actual_joint_balance_witness (r+4) (by omega) α ρ₀ sstar tstar epsBal ζBal
    hα hρ₀ hsstar htstar hepsBal hζBal
  obtain ⟨βcut,hβcut,hcut⟩:=marked_actual_inner_cut_event (r+4) (by omega) α ρ₀ sstar tstar kstar (1/100) 1 ζCut
    hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hζCut
  obtain ⟨βinner,hβinner,hinner⟩:=marked_actual_inner_balance_witness (r+4) (by omega) α ρ₀ sstar tstar epsBal ζBal
    hα hρ₀ hsstar htstar hepsBal hζBal
  obtain ⟨βcfg,hβcfg,hcfg⟩:=marked_actual_parent_configuration_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 ζCfg hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hζCfg
  obtain ⟨βactive,hβactive,hactive⟩:=marked_actual_next_active_all_parent_hubs_configuration_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 ζCfg hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hζCfg
  have hUpper:0<successorWeightUpper k₀ (α/4):=(successorWeightConstants_pos k₀ (α/4) (by positivity)).2
  obtain ⟨βwide,hβwide,hwide⟩:=marked_actual_next_active_nondeeper_hubs_load_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) tolLocal
    hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hUpper htolLocal
  obtain ⟨βrow,hβrow,hrow⟩:=marked_actual_next_active_nondeeper_hubs_rows_event r (r+4) (by omega) (by omega)
    α ρ₀ sstar tstar kstar (1/100) 1 rowErr hα hα1 hρ₀ hsstar htstar htstar1 hkstar (by norm_num) hrowErr
  let βmax:=min βparent (min βbalance (min βcut (min βinner (min βcfg (min βcommon (min βactive (min βwide βrow)))))))
  let βcap:=min βmax (min (1/4) (α/8))
  refine ⟨βcap,by dsimp [βcap,βmax];positivity,?_⟩
  intro ζCommon hζCommon size
  obtain ⟨a₀,b₀,e₀,hparent⟩:=hparent size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro εref δref β ε hεref hδref hb hbcap hbε he he1 ζWide ζRow hζWide hζRow f₀ d hd
  have hbmax:β≤βmax:=hbcap.trans (min_le_left _ _)
  have hbquarter:β≤1/4:=hbcap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbα:β≤α/8:=hbcap.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hbparent:β≤βparent:=hbmax.trans (min_le_left _ _)
  have hbbalance:β≤βbalance:=hbmax.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbcut:β≤βcut:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hbinner:β≤βinner:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hbcfg:β≤βcfg:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hbcommon:β≤βcommon:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
  have hbactive:β≤βactive:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))))
  have hbwide:β≤βwide:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))))
  have hbrow:β≤βrow:=hbmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))))
  obtain ⟨mParent,hmParent,hparent⟩:=hparent εref δref (1/100) β ε hεref hδref (by norm_num) hb hbparent hbε he he1 f₀ d hd
  obtain ⟨NBalance,hNBalance,mBalance,hmBalance,hbalance⟩:=hbalance ε he he1.le d hd
  obtain ⟨NCut,hNCut,hcut⟩:=hcut d hd
  obtain ⟨mCut,hmCut,hcut⟩:=hcut ε he he1.le
  obtain ⟨NInner,hNInner,mInner,hmInner,hinner⟩:=hinner ε he he1.le d hd
  obtain ⟨NCfg,hNCfg,hcfg⟩:=hcfg d hd
  obtain ⟨mCfg,hmCfg,hcfg⟩:=hcfg ε he he1.le
  obtain ⟨NCommon,hNCommon,hcommon⟩:=hcommon ζCommon hζCommon d hd
  obtain ⟨mCommon,hmCommon,hcommon⟩:=hcommon ε he he1.le
  obtain ⟨NActive,mActive,hNActive,hmActive,hactive⟩:=hactive d hd ε he he1.le
  obtain ⟨NWide,mWide,hNWide,hmWide,hwide⟩:=hwide d hd ε he he1.le ζWide hζWide
  obtain ⟨NRow,mRow,hNRow,hmRow,hrow⟩:=hrow d hd ε he he1.le ζRow hζRow
  obtain ⟨mFull,hmFull,hfull⟩:=marked_actual_parent_full_neighbourhood_event (r+12) d hd β ε ρ₀ tolRef (1/100) 1 pstarRef ζActive
    hb hbquarter he he1 hρ₀ htolRef (by norm_num) hpstarRef hζActive
  obtain ⟨mAgree,hmAgree,hagree⟩:=marked_actual_parent_spoke_agreement_event d hd β ε ρ₀ 1 pstarRef ζActive
    hb hbquarter he he1 hρ₀ hpstarRef hζActive
  obtain ⟨mActual,hmActual,hactual⟩:=marked_actual_parent_cuts_target_event α ρ₀ tstar kstar (1/100)
    hα hα1 hρ₀ htstar htstar1 hkstar (by norm_num) β ε hb hbα hbquarter he he1 d hd
  let m₀:ℕ:=mActual + mAgree + mFull + mParent + mBalance + NBalance + mCut + NCut + mInner + NInner + mCfg + NCfg + mCommon + NCommon + mActive + NActive + mWide + NWide + mRow + NRow + 800
  have hm₀:1≤m₀:=by dsimp [m₀];omega
  refine ⟨m₀,hm₀,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hmn Q π hpres hshort L hL W Z A B X f g ρ Dactive pstarLocal fParent gParent gWide ρParent Dparent
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  have hmActual':mActual≤m:=by dsimp [m₀] at hm;omega
  have hmAgree':mAgree≤m:=by dsimp [m₀] at hm;omega
  have hmFull':mFull≤m:=by dsimp [m₀] at hm;omega
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
  have hn800:800≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmRow':mRow≤m:=by dsimp [m₀] at hm;omega
  have hnRow:NRow≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmActive':mActive≤m:=by dsimp [m₀] at hm;omega
  have hnActive:NActive≤Fintype.card V:=by dsimp [m₀] at hm;omega
  have hmWide':mWide≤m:=by dsimp [m₀] at hm;omega
  have hnWide:NWide≤Fintype.card V:=by dsimp [m₀] at hm;omega
  obtain ⟨weightParent,weight,hwParent,hw,hparent⟩:=hparent V U G D m hreg hn hD hρlo hρhi hmParent' hmn Q π hpres hshort L hL
  refine ⟨weightParent,weight,hwParent,hw,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Eref EParent fCut gCut ρCut ECut EConfig EActive EWide ERow ECommon EFull EAgreement EActualCuts
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
  let errCommon:ℝ:=(1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+errCfg
  have hCommonBound:1-errCommon≤μ.probability (fun z=>ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by dsimp [errCommon];linarith only [hCommonProb']
  have hActiveProb:=hactive V U G D m β Q hreg hn hnActive hD hρlo hρhi hb hbactive hmActive' π hpres hshort L hL
    Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) errCommon hCommonBound
  have hActiveProb':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-errCommon≤μ.probability (fun z=>EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by exact hActiveProb
  let errActive:ℝ:=(1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+errCommon
  have hActiveBound:1-errActive≤μ.probability (fun z=>EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by dsimp [errActive];linarith only [hActiveProb']
  have hwNext:∀ i≤L,SuccessorSequenceWeightConditions (G.comap (f (i+1))) (ρ (i+1)) (3*d)
      (Dactive (i+1)) τ (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight (i+1)):=by
    intro i hi
    exact hw (i+1) (by omega)
  have hWideProb:=hwide V U G D m β Q hreg hn hnWide hD hρlo hρhi hb hbwide hmWide' π hpres hshort L hL
    (fun i=>weight (i+1)) hwNext Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
    (fun z=>EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) errActive hActiveBound
  have hWideProb':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-errActive≤μ.probability (fun z=>EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by exact hWideProb
  let errWide:ℝ:=(1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+errActive
  have hWideBound:1-errWide≤μ.probability (fun z=>EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by dsimp [errWide];linarith only [hWideProb']
  have hRowProb:=hrow V U G D m β Q hreg hn hnRow hD hρlo hρhi hb hbrow hmRow' π hpres hshort L hL
    Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
    (fun z=>EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) errWide hWideBound
  have hRowProb':1-(1/100:ℝ)-(Fintype.card V:ℝ)^(-(1:ℝ))-errWide≤μ.probability (fun z=>ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by exact hRowProb
  let errRow:ℝ:=(1/100:ℝ)+(Fintype.card V:ℝ)^(-(1:ℝ))+errWide
  have hRowBound:1-errRow≤μ.probability (fun z=>ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z):=by
    dsimp [errRow];linarith only [hRowProb']
  have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
    have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
    nlinarith [mul_nonneg hα.le hn0]
  have hmass:=marked_active_seed_mass_bound D ρ₀ tstar (s₀/((r+4:ℕ):ℝ)) pstarRef hρ₀ htstar hn hDhalf hρlo htlo hpstarRefBound
  have hFullProb:=hfull V U Γ Color G D m hreg hn hDhalf hρlo hρhi hmFull' hmn Q π hpres hshort L hL
    p kval (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2
    q hq hQ s hs hS a j (s₀/((r+4:ℕ):ℝ)) hq0 hmass
    (fun z=>ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) errRow hRowBound
  have hFullProb':1-errRow-2*(1/100:ℝ)-2*(Fintype.card V:ℝ)^(-(1:ℝ))≤
      μ.probability (fun z=>(ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z):=by exact hFullProb
  let errFull:ℝ:=errRow+2*(1/100:ℝ)+2*(Fintype.card V:ℝ)^(-(1:ℝ))
  have hFullBound:1-errFull≤μ.probability
      (fun z=>(ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z):=by
    dsimp [errFull];linarith only [hFullProb']
  have hAgreeProb:=hagree V U Γ Color G D m hreg hn hDhalf hρlo hρhi hmAgree' hmn Q π hpres hshort L hL
    p kval (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2
    q hq hQ s hs hS a j (s₀/((r+4:ℕ):ℝ)) hq0 hmass
    (fun z=>(ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) errFull hFullBound
  have hAgreeProb':1-errFull-(Fintype.card V:ℝ)^(-(1:ℝ))≤
      μ.probability (fun z=>((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z):=by exact hAgreeProb
  let errAgree:ℝ:=errFull+(Fintype.card V:ℝ)^(-(1:ℝ))
  have hAgreeBound:1-errAgree≤μ.probability
      (fun z=>((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z):=by
    dsimp [errAgree];linarith only [hAgreeProb']
  have hc:(1:ℝ)≤(r+4:ℕ):=by exact_mod_cast (show 1≤r+4 by omega)
  have hcpos:0<((r+4:ℕ):ℝ):=lt_of_lt_of_le (by norm_num) hc
  have hs0pos:0<s₀:=hsstar.trans_le hslo
  have hts:s₀/((r+4:ℕ):ℝ)≤s₀:=by
    apply (div_le_iff₀ hcpos).2
    nlinarith
  have htone:s₀/((r+4:ℕ):ℝ)≤1:=by linarith
  have hActualProb:=hactual V U Γ Color G D m hreg hn hD hρlo hρhi hmActual' Q π hpres hshort L hL
    p kval (densities.1.trans_le densities.2.1).le (densities.1.trans_le densities.2.2.1).le densities.2.2.2.2.2.2.2.2
    hpmin hkmin q hq hQ s hs hS a j s₀ (s₀/((r+4:ℕ):ℝ)) hq0 hs0 (horder.trans hslo) htlo htone hts
    (fun z=>((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z) errAgree hAgreeBound
  have hActualProb':1-(1/100:ℝ)-errAgree≤
      μ.probability (fun z=>EActualCuts z ∧ (((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z)):=by exact hActualProb
  have hn800r:(800:ℝ)≤Fintype.card V:=by exact_mod_cast hn800
  have hdiv:(23:ℝ)/(Fintype.card V:ℝ)≤23/800:=by apply (div_le_iff₀ hnpos).2;linarith
  have hExtra:(3/4:ℝ)≤μ.probability (fun z=>EActualCuts z ∧ (((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z)):=by
    dsimp [errAgree,errFull,errRow,errWide,errActive,errCommon,errCfg,errCut,errParent] at hActualProb'
    rw [hpow] at hActualProb'
    have heq:(23:ℝ)*(1/(Fintype.card V:ℝ))=23/(Fintype.card V:ℝ):=by ring
    rw [←heq] at hdiv
    linarith only [hActualProb',hdiv]
  by_cases hzero:L=0
  · have hresult:=hinner V U G D m β Q hreg hn hnInner hD hρlo hρhi hb hbinner hmInner' π hpres hshort L hL
      Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>EActualCuts z ∧ (((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z)) hExtra
    obtain ⟨z,hz,hi,hactual,⟨⟨hrow,hwide,hactive,hcommon,hcfg,hc,hp⟩,hfull⟩,hagree⟩:=hresult
    exact ⟨z,hz,hi,Or.inl hzero,hactual,hagree,hfull,hrow,hwide,hactive,hcommon,hcfg,hc,hp⟩
  · cases L with
    | zero => exact (hzero rfl).elim
    | succ jlevel =>
      have hjlen:jlevel+1<Q.length:=by omega
      have hresult:=hbalance V U G D m β Q hreg hn hnBalance hD hρlo hρhi hb hbbalance hmBalance' π hpres hshort jlevel hjlen
        Γ Color s₀ hslo hshi q hq hQ s hs hS a j hq0 hs0 htlo (fun z=>EActualCuts z ∧ (((ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z) ∧ EFull z) ∧ EAgreement z)) hExtra
      obtain ⟨z,hz,hi,hd,hactual,⟨⟨hrow,hwide,hactive,hcommon,hcfg,hc,hp⟩,hfull⟩,hagree⟩:=hresult
      refine ⟨z,hz,?_,?_,hactual,hagree,hfull,hrow,hwide,hactive,hcommon,hcfg,hc,hp⟩
      · simpa only [Nat.succ_eq_add_one] using hi
      · right
        simpa using hd
end Oberwolfach
