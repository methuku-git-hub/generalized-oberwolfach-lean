module

public import Oberwolfach.MarkedVortexEndpointRecordInputs
public import Oberwolfach.MarkedVortexInnerCutFieldsUniform
public import Oberwolfach.MarkedVortexInnerDomainsNonempty
public import Oberwolfach.MarkedVortexNestedActiveRowsLoads
public import Oberwolfach.MarkedVortexActualBalanceRecordInputs
public import Oberwolfach.MarkedVortexParentLoadRecordInputs
public import Oberwolfach.MarkedVortexReferenceActualCutRecordInputs
public import Oberwolfach.MarkedVortexParentNeighbourhoodRecordInputs
public import Oberwolfach.MarkedJointCutDensityWeightsSeparateScales
public import Oberwolfach.MarkedVortexJointConfigurationRecordInputs
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
theorem marked_joint_actual_reference_all_levels_endpoint_record_fields_with_weights_separate_scales
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
    ∃ βmax:ℝ,0<βmax ∧ ∀ ζCommon:ℝ,0<ζCommon→
    ∀ εref δref β ε:ℝ,
    0<εref→0<δref→0≤β→β≤βmax→β≤εref/4→0<ε→ε<1/4→
    ∀ ζWide ζRow:ℝ,0<ζWide→0<ζRow→∀ (d:ℕ) (hd:2≤d),∃ m₀:ℕ,1≤m₀ ∧
    ∀ size:ℕ,∃ a₀ b₀ e₀:ℕ,∀ f₀:ℕ,∃ n₀:ℕ,
    ∀ (V U:Type) [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
      (G:SimpleGraph V) (D m:ℕ),G.IsRegularOfDegree D→∀ (hn:0<Fintype.card V),
    (1/2+α)*Fintype.card V≤(D:ℝ)→∀ (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    m₀≤m→n₀≤Fintype.card V→m≤Fintype.card V→∀ (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
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
        (markedVortexDeeperVertices Q) (markedVortexDeeperHubs Q) z) ∧ EActualCuts z ∧ EAgreement z ∧ EFull z ∧ ERow z ∧ EWide z ∧ EActive z ∧ ECommon z ∧ EConfig z ∧ ECut z ∧ EParent z ∧
      (∀ βA βrec κ:ℝ, βA≤βCommon → ζCommon≤κ/4 →
        3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg →
        3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg →
        βrec≤βA → tolRef+(r+12:ℕ)*ζActive≤κ/4 → ζActive≤κ/4 → εref=κ/4 → δref=κ →
        ∀ thetaDeep:ℝ,
        τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent≤κ/4 →
        τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent≤thetaDeep/4 →
        ∀ etaBal x:ℝ,0≤x → epsBal+((r+4)+2:ℕ)*ζBal≤etaBal →
        epsBal+((r+4)+2:ℕ)*ζBal≤x/2 → L+1=Q.length →
        ∀ eta:ℝ, rowErr+ζRow≤(s₀/((r+4:ℕ):ℝ))/8 →
        τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide≤eta/4 →
        ∀ deltaI hIcut:ℝ, β≤1/4 → 0≤hIcut → deltaI≤(α/2)/32 → deltaI≤kstar/32 →
        2*deltaI≤tstar/8 → 2*hIcut≤(α/2)*kstar/4 → 2*hIcut≤tstar/8-ζCut →
        tolRef+h*ζActive≤x/2 →
    (∀ i≤L,
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:markedVortexNonDeeperHubType Q i→markedVortexHubType Q i:=Subtype.val
      let ρP:=markedVortexPermutation Q π hpres i
      let ρ:=markedVortexActivePermutation Q π hpres (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      MarkedCommonConfigurationsWithSpokes r (G.comap fP) ρP d βA (κ/4) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r (G.comap fP) ρP d Finset.univ
        (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) (3*(min βA ((s₀/((r+4:ℕ):ℝ))/4))) σP HP ∧
      MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (f x))) ρ d Finset.univ
        (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP)
        (fun b x u=>HP b (fA (f x)) (gA u))) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i; let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i; let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i; let σ:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u);
      MarkedRowsWithSpokes (G.comap f) ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
      (∀ b x,(∑ u,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
      (∀ b u,(∑ x,if ¬(rawMarkedPairSpokes ρ d σ a j b x u↔H b x u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W)) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let rho:=initialIndexDensity U D
      let c:ℝ:=(r+4:ℕ)
      let t:=s₀/c
      let pRef:=rho*c*t/2
      let kRef:=pRef/c
      let DRef:=2*(Fintype.card Z:ℝ)/rho
      let σ:=rawMarkedRestrictPair f g z.1;
      MarkedReferenceStatistics (G.comap f) ρ d a j DRef (κ/4) κ (2*(α/16)) pRef kRef (c*t) t σ ∧
      MarkedReferenceCutFamilies (G.comap f) ρ d a j (2*(α/16)) pRef kRef t σ) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let P:=G.comap (markedVortexVertexEmbedding Q i)
      let ρ:=markedVortexPermutation Q π hpres i
      let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D
      let σ:=rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b
        (markedVortexVertexEmbedding Q i x) (markedVortexHubEmbedding Q i u)
      let qi:=fun u=>q (markedVortexHubEmbedding Q i u)
      let si:=fun u=>s (markedVortexHubEmbedding Q i u);
      MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent i) (thetaDeep/4) σ H ∧
      (let seed:=fun X:MarkedWheel (Prod.fst:W×W→W) Prod.snd Prod.fst Prod.snd (r+4) ρ (3*d)
          (fun (_:W) (_:Z)=>True) (fun _ _=>True)=>weightParent i X.1.val/(Dload*p^(r+4)*kval*s₀^(r+4));
        ∀ root:((W×W)⊕(W×W))⊕(Bool×W×Z),
          rawMarkedWheelMarginal P ρ d p kval qi si a j root≠0→
          |typedMarkedPotentialLoad seed (rawMarkedPairRims P ρ d σ) H root-1|≤κ/4)) ∧
    (∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let f:=markedVortexVertexEmbedding Q i
      let g:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let σ:=rawMarkedRestrictPair f g z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (f x) (g u)
      let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) false
      let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ (Sum.inl e)) true
      let S:=Finset.univ.filter (fun s:W×Z=>H false s.1 s.2∨H true s.1 s.2)
      let I:=markedVortexInnerVertices Q i
      let J:=markedVortexInnerHubs Q i
      let T:=markedVortexDeeperVertices Q i
      let R:=markedVortexDeeperHubs Q i
      let bal:=markedFiniteDomainBalance (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) (H true) Finset.univ S (r+4);
      ∃ errInner errDeep:ℝ, 0≤errDeep ∧
      errInner≤(x/2)*Fintype.card W ∧ errDeep≤(x/2)*Fintype.card W ∧
      (∀ v j,|bal I J v j|≤errInner) ∧
      (∀ v j,|bal T R v j|≤errDeep) ∧
      (∀ v j,|bal I J v j|≤etaBal*I.card)) ∧
    (∀ i≤L,
      let Z:=markedVortexHubType Q i
      let Zkeep:=markedVortexNonDeeperHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:Zkeep→Z:=Subtype.val
      let ρ:=markedVortexActivePermutation Q π hpres (i+1)
      let σP:=rawMarkedRestrictPair fP gP z.1
      let HP:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
          (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d 1 Finset.univ p kval
        (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
        (((s₀/((r+4:ℕ):ℝ))/8)*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q (i+1)):Finset (markedVortexVertexType Q (i+1))))
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u)) ∧
      MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (f x))) ρ d (r+4) (Dactive (i+1)) p kval s₀ (weight (i+1)) (eta/4)
        (rawMarkedRestrictPair (fun x=>fA (f x)) gA σP) (fun b x u=>HP b (fA (f x)) (gA u))) ∧
    (∀ i≤L,
    (∀ mark,BipartiteLargeCut
      (fun x:↥(markedVortexInnerVertices Q i)=>fun y:↥(markedVortexInnerVertices Q i)=>
        markedPhysicalRim (G.comap (markedVortexVertexEmbedding Q i)) (markedVortexPermutation Q π hpres i) (3*d)
          (fun e=>rawMarkedRestrictPair (markedVortexVertexEmbedding Q i) (markedVortexHubEmbedding Q i) z.1 (Sum.inl e)) mark x.val y.val) deltaI (2*hIcut)) ∧
    (∀ mark,BipartiteLargeCut (relationMultiplicity (fun x:↥(markedVortexInnerVertices Q i)=>fun u:↥(markedVortexInnerHubs Q i)=>
      retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j mark
        (markedVortexVertexEmbedding Q i x.val) (markedVortexHubEmbedding Q i u.val))) deltaI (2*hIcut))) ∧
    ∀ i≤L,
      let W:=markedVortexVertexType Q i
      let Z:=markedVortexHubType Q i
      let fP:=markedVortexVertexEmbedding Q i
      let gP:=markedVortexHubEmbedding Q i
      let ρ:=markedVortexPermutation Q π hpres i
      let fA:=markedVortexNonDeeperVertexEmbedding Q i
      let f:=markedVortexNextActiveInNonDeeper Q i
      let gA:=markedVortexNonDeeperHubToParent Q i
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q i
      let ω:=rawMarkedRestrictPair fP gP z.1
      let H:=fun b x u=>retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
        (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H)  :=by
  obtain ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βCommon,hβconfig,hβCommon,hbase⟩:=
    marked_joint_actual_reference_all_levels_actual_cut_density_with_weights_separate_scales r h k₀ hr hlen α ρ₀ sstar tstar kstar
      hα hα1 hρ₀ hsstar htstar htstar1 horder hkstar hmargin
  refine ⟨εAbs,ζAbs,δAbs,hεAbs,hζAbs,hδAbs,βconfig,βCommon,hβconfig,hβCommon,?_⟩
  intro tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr
    htolRef hpstarRef hpstarRefBound hζActive hτ htolLocal hζLocal hτParent htolParent hζParent hepsBal hζBal hζCut hζCfg hrowErr
  obtain ⟨βmax,hβmax,hbase⟩:=hbase tolRef pstarRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr
    htolRef hpstarRef hpstarRefBound hζActive hτ htolLocal hζLocal hτParent htolParent hζParent hepsBal hζBal hζCut hζCfg hrowErr
  refine ⟨βmax,hβmax,?_⟩
  intro ζCommon hζCommon εref δref β ε hεref hδref hb hbmax hbε he he1 ζWide ζRow hζWide hζRow d hd
  obtain ⟨m₀,hm₀,hbase⟩:=hbase ζCommon hζCommon εref δref β ε hεref hδref hb hbmax hbε he he1 ζWide ζRow hζWide hζRow d hd
  refine ⟨m₀,hm₀,?_⟩
  intro size
  obtain ⟨a₀,b₀,e₀,hbase⟩:=hbase size
  refine ⟨a₀,b₀,e₀,?_⟩
  intro f₀
  obtain ⟨n₀,hbase⟩:=hbase f₀
  refine ⟨n₀,?_⟩
  intro V U _ _ _ _ G D m hreg hn hD hρlo hρhi hm hnBound hmn Q π hpres hshort L hL W Z A B X f g ρ Dactive pstarLocal fParent gParent gWide ρParent Dparent
  letI : Nonempty V:=Fintype.card_pos_iff.mp hn
  obtain ⟨weightParent,weight,hwParent,hw,hbase⟩:=hbase V U G D m hreg hn hD hρlo hρhi hm hnBound hmn Q π hpres hshort L hL
  refine ⟨weightParent,weight,hwParent,hw,?_⟩
  intro Γ Color _ _ s₀ hslo hshi dens densities p kval hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo Eref EParent fCut gCut ρCut ECut EConfig EActive EWide ERow ECommon EFull EAgreement EActualCuts
  obtain ⟨z,hMass,hBal,hDeep,hActual,hAgree,hFull,hRow,hWide,hActive,hCommon,hConfig,hCut,hParent⟩:=
    hbase Γ Color s₀ hslo hshi hpmin hkmin q hq hQ s hs hS a j hq0 hs0 htlo
  refine ⟨z,hMass,hBal,hDeep,hActual,hAgree,hFull,hRow,hWide,hActive,hCommon,hConfig,hCut,hParent,?_⟩
  intro βA βrec κ hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq thetaDeep hpot hdeep etaBal x hx hbal hmargin hterminal eta hrowmargin hloadmargin deltaI hIcut hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
  constructor
  · exact marked_vortex_joint_configuration_record_inputs Q π hpres r d L a j βCommon ζCommon βA βrec κ
      (s₀/((r+4:ℕ):ℝ))
      (markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
      (markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
      hβA hζκ hC hP hrec z hCommon hConfig hActive
  · constructor
    · have hDpos:0<D:=by
        have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
        have hh:0<(1/2+α)*Fintype.card V:=by positivity
        exact_mod_cast hh.trans_le hD
      exact marked_vortex_parent_neighbourhood_record_inputs r d G D m β ε Q π hpres hreg hn hDpos hρhi he.le L hL
        p kval tolRef ζActive κ (by positivity) herr hζActiveK q s a j z hFull hAgree
    · constructor
      · have hρ:0≤ initialIndexDensity U D:=by linarith
        have hs₀:0≤s₀:=le_trans hsstar.le hslo
        have href:MarkedReferenceActiveAbsorberProperty r h d (α/2) βconfig (κ/4) κ tolRef ζActive ζAbs tstar εAbs
            size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ (initialIndexDensity U D*s₀/2)
            ((initialIndexDensity U D*s₀/2)/((r+4:ℕ):ℝ)) q s a j z:=by
          simpa only [hεeq,hδeq] using hParent.2.2
        exact marked_vortex_reference_actual_cut_record_inputs r h d α βconfig κ tolRef ζActive ζAbs tstar εAbs
          hα.le size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ hs₀ hρ q s a j z href hActual
      · constructor
        · exact marked_vortex_parent_load_record_inputs Q π hpres d (r+4) L a j p kval s₀
            (τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*ζParent)
            (33*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))) κ thetaDeep
            hpot hdeep q s weightParent z hParent.1
        · constructor
          · exact marked_vortex_actual_balance_record_inputs Q π hpres d (r+4) L a j epsBal ζBal etaBal x
              hepsBal.le hζBal.le hx hbal hmargin hterminal z hBal hDeep
          · constructor
            · exact marked_vortex_nested_active_rows_and_loads Q π hpres L d (r+4) p kval s₀
                (s₀/((r+4:ℕ):ℝ)) (rowErr+ζRow)
                (τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide)
                eta hrowmargin hloadmargin q s a j (fun i=>Dactive (i+1)) (fun i=>weight (i+1)) z hRow hWide
            · constructor
              · intro i hi
                have hDhalf:(Fintype.card V:ℝ)/2≤D:=by
                  have hn0:(0:ℝ)≤Fintype.card V:=Nat.cast_nonneg _
                  nlinarith [mul_nonneg hα.le hn0]
                have hmpos:0<m:=lt_of_lt_of_le (by omega) hm
                obtain ⟨hnI,huI⟩:=marked_vortex_inner_domains_nonempty Q hreg hn hDhalf hρ₀ hρlo hb hbquarter he hmpos i (by omega)
                exact marked_vortex_inner_cut_fields_uniform_densities Q π hpres d i a j z
                  (α/2) p kval kstar tstar ζCut deltaI (2*hIcut) hnI huI (by positivity) hpmin hkmin
                  (by positivity) hδα hδstar hδt hhstar hhs (hCut i hi)
              · have hDpos:0<D:=by
                  have hnpos:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
                  have hh:0<(1/2+α)*Fintype.card V:=by positivity
                  exact_mod_cast hh.trans_le hD
                exact marked_vortex_endpoint_record_inputs r h d (α/2) βconfig εref δref tolRef ζActive ζAbs tstar εAbs
                  size a₀ b₀ e₀ f₀ G D m β ε Q π hpres hreg hn hDpos hρhi he.le L hL s₀ p kval x
                  (by positivity) hEndpoint q s a j z hParent.2.2
end Oberwolfach
