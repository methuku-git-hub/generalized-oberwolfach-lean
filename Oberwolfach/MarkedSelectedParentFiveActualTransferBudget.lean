module

public import Oberwolfach.MarkedSelectedParentThreeTransferBudget
public import Oberwolfach.MarkedVortexInitialBalanceFromSelectedParent
public import Oberwolfach.MarkedVortexInitialBoundaryFromParentRecord

@[expose] public section
/-! Select one change tolerance for the common, deeper and first-active
transfers. All three can then be applied to the same selected sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_selected_parent_five_actual_transfers_and_potential_budget
    (r h k₀ d:ℕ) (κ αCommon ω plo klo αCfg ζDeep theta B pstar:ℝ)
    (α ρ₀ sstar tstar kstar etaBal x iota:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow η:ℝ)
    (hκ:0<κ) (hαCommon:0<αCommon) (hω:0<ω) (hp:0<plo) (hk:0<klo)
    (hζDeep:0<ζDeep) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar)
    (hζCfg:0<ζCfg) (hη:0<η) (htstar:0<tstar) (hηBal:0<etaBal) (hx:0<x) (hiota:0 < iota):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    (
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (h k₀ d:ℕ) (ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζDeep rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec thetaDeep etaBal x eta deltaI hIcut:ℝ)
    (hpEq:p=initialIndexDensity U D*s₀/2) (hkEq:kval=p/((r+4:ℕ):ℝ))
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hraw:σold=z.1)
    (hspokes:Hold=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
    (hGood:MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d αCommon ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζDeep rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (hβA:βA≤βCommon) (hζκ:ζCommon≤(κ/2)/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (αCommon/2) (tstar/2) kstar-(r+5:ℕ)*ζDeep)
    (hP:3*βA≤markedLocalPathCoefficient r (αCommon/2) (tstar/2) kstar-(r+4:ℕ)*ζDeep)
    (hrec:βrec≤βA) (herr:tolRef+(r+12:ℕ)*ζActive≤(κ/2)/4) (hζActiveK:ζActive≤(κ/2)/4)
    (hεeq:εref≤(κ/2)/4) (hδeq:δref=κ/2)
    (hpot:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αCommon/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤(κ/2)/4)
    (hdeep:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αCommon/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤thetaDeep/4)
    (hx:0≤x) (hbal:epsBal+((r+4)+2:ℕ)*ζBal≤etaBal)
    (hmargin:epsBal+((r+4)+2:ℕ)*ζBal≤x/2) (hterminal:L+1=Q.length)
    (hrowmargin:rowErr+ζRow≤(s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αCommon/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide≤eta/4)
    (hbquarter:β≤1/4) (hh:0≤hIcut) (hδα:deltaI≤(αCommon/2)/32) (hδstar:deltaI≤kstar/32)
    (hδt:2*deltaI≤tstar/8) (hhstar:2*hIcut≤(αCommon/2)*kstar/4) (hhs:2*hIcut≤tstar/8-ζCut)
    (hEndpoint:tolRef+h*ζActive≤x/2)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hn:0<Fintype.card V) (hU:ω*Fintype.card V≤(Fintype.card U:ℝ))
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e)→markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (htypes:∀v u,¬(Hold false v u∧Hold true v u))
    (hplo:plo≤p) (hklo:klo≤kval),
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hpres 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σglobal
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let c:ℝ:=(r+4:ℕ)
    let t:=s₀/c
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D;
    MarkedReferenceStatistics P ρ d a j Dload (κ/4) κ (αCommon/16) p kval (c*t) t σ ∧
    MarkedReferenceCutFamilies P ρ d a j (αCommon/16) p kval t σ ∧
    MarkedCommonConfigurationsWithSpokes r P ρ d βA (κ/4) σ H ∧
    MarkedRowsWithSpokes P ρ d (r+12) Finset.univ p kval (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    MarkedIndicesWithSpokes ρ d (r+12) Finset.univ (fun u=>q (g u)) (fun u=>s (g u)) a j ((κ/4)*Fintype.card W) σ H ∧
    (∀b v,(∑u,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card Z) ∧
    (∀b u,(∑v,if ¬(rawMarkedPairSpokes ρ d σ a j b v u↔H b v u) then (1:ℝ) else 0)≤(κ/4)*Fintype.card W)
    ) ∧
    (
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (h k₀ d:ℕ) (α ρ₀ sstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζDeepOld rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaOld etaBal x eta deltaI hIcut A:ℝ)
    (hpEq:p=initialIndexDensity U D*s₀/2) (hkEq:kval=p/((r+4:ℕ):ℝ))
    (htheta:thetaOld≤theta/2)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hraw:σold=z.1)
    (hspokes:Hold=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
    (hGood:MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζDeepOld rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (hβA:βA≤βCommon) (hζκ:ζCommon≤κ/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζDeepOld)
    (hP:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζDeepOld)
    (hrec:βrec≤βA) (herr:tolRef+(r+12:ℕ)*ζActive≤κ/4) (hζActiveK:ζActive≤κ/4)
    (hεeq:εref≤κ/4) (hδeq:δref=κ)
    (hcfgα:αCfg=α/2) (hcfgζ:ζDeep=2*ζDeepOld)
    (hpot:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤κ/4)
    (hdeep:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent≤thetaOld/4)
    (hx:0≤x) (hbal:epsBal+((r+4)+2:ℕ)*ζBal≤etaBal)
    (hmargin:epsBal+((r+4)+2:ℕ)*ζBal≤x/2) (hterminal:L+1=Q.length)
    (hrowmargin:rowErr+ζRow≤(s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide≤eta/4)
    (hbquarter:β≤1/4) (hh:0≤hIcut) (hδα:deltaI≤(α/2)/32) (hδstar:deltaI≤kstar/32)
    (hδt:2*deltaI≤tstar/8) (hhstar:2*hIcut≤(α/2)*kstar/4) (hhs:2*hIcut≤tstar/8-ζCut)
    (hEndpoint:tolRef+h*ζActive≤x/2)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (hn:0<Fintype.card V)
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e)→markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)
    (htypes:∀v u,¬(Hold false v u∧Hold true v u)),
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hpres 0
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g σold
    let σ':=rawMarkedRestrictPair f g σglobal
    let H:=fun b v u=>Hold b (f v) (g u)
    let H':=fun b v u=>Hglobal b (f v) (g u)
    let c:ℝ:=(r+4:ℕ)
    let t:=s₀/c
    let Dload:=2*(Fintype.card Z:ℝ)/initialIndexDensity U D;
    3*βA≤markedLocalCycleCoefficient r αCfg (tstar/2) kstar-(r+5:ℕ)*ζDeep→
    3*βA≤markedLocalPathCoefficient r αCfg (tstar/2) kstar-(r+4:ℕ)*ζDeep→
    (Fintype.card W:ℝ)/2≤Dload→Dload≤2*Fintype.card W→
    pstar≤p→pstar≤kval→pstar≤s₀→p≤1→kval≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) Dload τParent A B (weightParent 0)→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent 0) (theta/4) σ' H'
    ) ∧
    (
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(G:SimpleGraph V) (Dnat mm:ℕ) (β ε:ℝ) (Q:Vortex U G Dnat β ε mm)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (L:ℕ) (s₀ p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
      (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
      (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
      (size a₀ b₀ e₀ f₀:ℕ)
      (hGood:MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d α ρ₀ sstar tstar kstar
        εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
        size a₀ b₀ e₀ f₀ G Dnat mm β ε Q π hπ L s₀ p k q s a j weightParent weight z)
      (τglobal:RawMarkedOutcome V U Γ Color) (Hglobal':Bool→V→U→Prop),
    let W:=↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))
    let Z:=markedVortexNonDeeperHubType Q 0
    let f:=markedVortexActiveVertexEmbedding Q 1
    let g:=markedVortexNonDeeperHubToPhysical Q 0
    let ρ:=markedVortexActivePermutation Q π hπ 1
    let P:=G.comap f
    let σ:=rawMarkedRestrictPair f g z.1
    let corrected:=rawMarkedRestrictPair f g τglobal
    let Hglobal:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j
    let H:=fun b v u=>Hglobal b (f v) (g u)
    let H':=fun b v u=>Hglobal' b (f v) (g u)
    let Dactive:=2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U Dnat
    let pstarLocal:=ρ₀*sstar/(2*((r+4:ℕ):ℝ))
    let err:=τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/pstarLocal^(2*(r+4)+1))*(4/ε)*ζWide;
    rawMarkedPairRims P ρ d corrected=rawMarkedPairRims P ρ d σ→
    ∀(FS:SimpleGraph (W⊕Z)),
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀u,(FS.degree (Sum.inr u):ℝ)≤ζ*Fintype.card W)→
    ∀(t βrec:ℝ),0<Fintype.card W→
    3*βrec≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*(2*ζCfg)→
    3*βrec≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*(2*ζCfg)→
    βrec≤t/4→tstar≤t→err≤η/8→ rowErr+ζRow≤tstar/16→
    (Fintype.card W:ℝ)/2≤Dactive→Dactive≤2*Fintype.card W→
    pstar≤p→pstar≤k→pstar≤s₀→p≤1→k≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) Dactive τ (successorWeightLower k₀ (α/4)) B (weight 1)→
    let fP:=markedVortexVertexEmbedding Q 0
    let gP:=markedVortexHubEmbedding Q 0
    let fA:=markedVortexNonDeeperVertexEmbedding Q 0
    let fnext:=markedVortexNextActiveInNonDeeper Q 0
    let gA:=markedVortexNonDeeperHubToParent Q 0
    let τP:=rawMarkedRestrictPair fP gP τglobal
    let HP:=fun b x u=>Hglobal' b (fP x) (gP u);
    MarkedLocalConfigurationsWithSpokes r ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d Finset.univ
      (3*βrec) (3*βrec) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedRowsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d 1 Finset.univ p k (fun u=>q (gP (gA u))) (fun u=>s (gP (gA u))) a j
      ((t/8)*Fintype.card W) (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u)) ∧
    MarkedLocalSpokeLoadsWithSpokes ((G.comap fP).comap (fun x=>fA (fnext x))) ρ d (r+4) Dactive p k s₀ (weight 1) (η/4)
      (rawMarkedRestrictPair (fun x=>fA (fnext x)) gA τP) (fun b x u=>HP b (fA (fnext x)) (gA u))
    ) ∧
    ((κ/2)/4+33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))*ζ≤κ/4) ∧
    (
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀(G:SimpleGraph V) (D m:ℕ) (β ε:ℝ) (Q:Vortex U G D β ε m)
      (π:Equiv.Perm V) (hπ:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
      (d L:ℕ) (a:Γ) (j:Color) (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
      (h k₀:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
      (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τLevel tolLocal ζLocal τParent tolParent ζParent ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
      (size a₀ b₀ e₀ f₀:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ)
      (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
      (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
      (τ:RawMarkedOutcome V U Γ Color) (H':Bool→V→U→Prop)
      (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U)) (epsBal ζbal:ℝ),
    0≤epsBal→0≤ζbal→epsBal+((r+4)+2:ℕ)*ζbal≤etaBal/2→
    epsBal+((r+4)+2:ℕ)*ζbal≤x/4→L+1=Q.length→
    MarkedVortexParentRecordSmallerReferenceEvent r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τLevel tolLocal ζLocal τParent tolParent ζParent epsBal ζbal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hπ L s₀ p kval q s a j weightParent weight z→
    let σ:=z.1
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j;
    (∀e,σ (Sum.inr e)=τ (Sum.inr e))→
    (∀a,¬(rawMarkedPairRims G π d σ a↔rawMarkedPairRims G π d τ a)→markedPairPhysical π a∈FR.edgeFinset)→
    (∀b v u,¬(H b v u↔H' b v u)→FS.Adj (Sum.inl v) (Sum.inr u))→
    (∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V)→(∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V)→
    (∀v u,¬(H false v u∧H true v u))→(∀v u,¬(H' false v u∧H' true v u))→
    let W:=markedVortexVertexType Q 0
    let Z:=markedVortexHubType Q 0
    let f:=markedVortexVertexEmbedding Q 0
    let g:=markedVortexHubEmbedding Q 0
    let ρ:=markedVortexPermutation Q π hπ 0
    let σ₀:=rawMarkedRestrictPair f g σ
    let τ₀:=rawMarkedRestrictPair f g τ
    let H₀:=fun b v u=>H b (f v) (g u)
    let H₀':=fun b v u=>H' b (f v) (g u)
    let I:=markedVortexInnerVertices Q 0
    let J:=markedVortexInnerHubs Q 0
    let T:=markedVortexDeeperVertices Q 0
    let R:=markedVortexDeeperHubs Q 0
    let E:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) false
    let K:=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>σ₀ (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:W×Z=>H₀ false z.1 z.2∨H₀ true z.1 z.2)
    let E':=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>τ₀ (Sum.inl e)) false
    let K':=MarkedSampleArc (G.comap f) ρ (3*d) (fun e=>τ₀ (Sum.inl e)) true
    let S':=Finset.univ.filter (fun z:W×Z=>H₀' false z.1 z.2∨H₀' true z.1 z.2);
    iota*Fintype.card W≤(I.card:ℝ)→
    ∃errI errT:ℝ,0≤errT ∧ errI≤(x/2)*Fintype.card W ∧ errT≤(x/2)*Fintype.card W ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤errI) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) T R v j|≤errT) ∧
      (∀v j,|markedFiniteDomainBalance (fun e:E'=>e.val.1) (fun e=>e.val.2)
        (fun e:K'=>e.val.1) (fun e=>e.val.2) (H₀' true) Finset.univ S' (r+4) I J v j|≤etaBal*I.card)
    ) ∧
    (
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i v,π v∈Q.extendedVertices i↔v∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color) (Hold Hglobal:Bool→V→U→Prop)
    (βA βrec κ thetaDeep etaBal xold eta deltaI hIcut:ℝ) (hxold:xold≤x/2)
    (hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κ thetaDeep etaBal xold eta deltaI hIcut)
    (FR:SimpleGraph V) (FS:SimpleGraph (V⊕U))
    (hinterval:∀e,σold (Sum.inr e)=σglobal (Sum.inr e))
    (hR:∀e,¬(rawMarkedPairRims G π d σold e↔rawMarkedPairRims G π d σglobal e)→markedPairPhysical π e∈FR.edgeFinset)
    (hS:∀b v u,¬(Hold b v u↔Hglobal b v u)→FS.Adj (Sum.inl v) (Sum.inr u))
    (hFR:∀v,(FR.degree v:ℝ)≤ζ*Fintype.card V) (hFS:∀z,(FS.degree z:ℝ)≤ζ*Fintype.card V),
    (let W:=markedVortexVertexType Q 0
      let Z:=markedVortexHubType Q 0
      let fP:=markedVortexVertexEmbedding Q 0
      let gP:=markedVortexHubEmbedding Q 0
      let ρ:=markedVortexPermutation Q π hpres 0
      let fA:=markedVortexNonDeeperVertexEmbedding Q 0
      let f:=markedVortexNextActiveInNonDeeper Q 0
      let gA:=markedVortexNonDeeperHubToParent Q 0
      let X:=Finset.univ.image f
      let Zinner:=markedVortexInnerNonDeeperHubs Q 0
      let ω:=rawMarkedRestrictPair fP gP σglobal
      let H:=fun b x u=>Hglobal b (fP x) (gP u);
      ∃ errR errI:ℝ,0≤errR ∧ 0≤errI ∧ errR≤(x/2)*Fintype.card W ∧ errI≤(x/2)*Fintype.card W ∧
        MarkedRowsWithSpokes (G.comap fP) ρ d h (X.image fA) p kval (fun u=>q (gP u)) (fun u=>s (gP u)) a j errR ω H ∧
        MarkedIndicesWithSpokes ρ d h (Zinner.image gA) (fun u=>q (gP u)) (fun u=>s (gP u)) a j errI ω H)
    ) :=by
  obtain ⟨capThree,hThree,hThreeApply⟩:=
    marked_selected_parent_common_deep_active_shared_change_budget r h k₀ d κ αCommon ω plo klo αCfg ζDeep theta B pstar
      α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow η
      hκ hαCommon hω hp hk hζDeep hθ hB hpstar hζCfg hη htstar
  obtain ⟨capBalance,hBalance,hBalanceApply⟩:=
    marked_vortex_initial_record_balance_from_selected_parent r etaBal x iota hηBal hx hiota
  obtain ⟨capBoundary,hBoundary,hBoundaryApply⟩:=
    marked_vortex_initial_boundary_from_parent_record h x hx
  let C:ℝ:=33*((r+4:ℝ)+1)^4*(2*B/pstar^(2*(r+4)+1))
  have hC:0≤C:=by dsimp [C];positivity
  have hden:0<8*(1+C):=by positivity
  let cap:ℝ:=min capThree (min capBalance (min capBoundary (κ/(8*(1+C)))))
  have hcap:0<cap:=by dsimp [cap];positivity
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hz
  have ht:ζ≤capThree:=hz.trans (min_le_left _ _)
  have hb:ζ≤capBalance:=hz.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbd:ζ≤capBoundary:=hz.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hp:ζ≤κ/(8*(1+C)):=hz.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hscaled:ζ*(8*(1+C))≤κ:=(le_div_iff₀ hden).mp hp
  have hpot:(κ/2)/4+C*ζ≤κ/4:=by nlinarith only [hscaled,hζ]
  have hfields:=hThreeApply ζ hζ ht
  exact ⟨hfields.1,hfields.2.1,hfields.2.2,by simpa only [C] using hpot,
    hBalanceApply ζ hζ hb,hBoundaryApply ζ hζ hbd⟩
end Oberwolfach
