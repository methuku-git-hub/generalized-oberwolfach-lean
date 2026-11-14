module

public import Oberwolfach.MarkedVortexInitialCommonFromSelectedParent
public import Oberwolfach.MarkedVortexInitialDeepFromActualParent

@[expose] public section
/-! A single change budget can be chosen before sampling for both the
common and deeper corrected fields, each retaining its selected parent event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 50000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_selected_parent_common_deep_shared_change_budget
    (r:ℕ) (κ αCommon ω plo klo αCfg tstar kstar ζCfg theta B pstar:ℝ)
    (hκ:0<κ) (hα:0<αCommon) (hω:0<ω) (hp:0<plo) (hk:0<klo)
    (hζCfg:0<ζCfg) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
    (
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [Nonempty V] [DecidableEq U],
    ∀ (h k₀ d:ℕ) (ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
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
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (hβA:βA≤βCommon) (hζκ:ζCommon≤(κ/2)/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (αCommon/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hP:3*βA≤markedLocalPathCoefficient r (αCommon/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
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
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfgOld rowErr ζCommon ζWide ζRow:ℝ)
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
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfgOld rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (hβA:βA≤βCommon) (hζκ:ζCommon≤κ/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*ζCfgOld)
    (hP:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*ζCfgOld)
    (hrec:βrec≤βA) (herr:tolRef+(r+12:ℕ)*ζActive≤κ/4) (hζActiveK:ζActive≤κ/4)
    (hεeq:εref≤κ/4) (hδeq:δref=κ)
    (hcfgα:αCfg=α/2) (hcfgζ:ζCfg=2*ζCfgOld)
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
    3*βA≤markedLocalCycleCoefficient r αCfg (tstar/2) kstar-(r+5:ℕ)*ζCfg→
    3*βA≤markedLocalPathCoefficient r αCfg (tstar/2) kstar-(r+4:ℕ)*ζCfg→
    (Fintype.card W:ℝ)/2≤Dload→Dload≤2*Fintype.card W→
    pstar≤p→pstar≤kval→pstar≤s₀→p≤1→kval≤1→s₀≤1→
    SuccessorSequenceWeightConditions P ρ (3*d) Dload τParent A B (weightParent 0)→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent 0) (theta/4) σ' H'
    ) :=by
  obtain ⟨capCommon,hCommon,hCommonApply⟩:=
    marked_vortex_initial_common_from_selected_parent r κ αCommon ω plo klo hκ hα hω hp hk
  obtain ⟨capDeep,hDeep,hDeepApply⟩:=
    marked_vortex_initial_deep_from_actual_parent r αCfg tstar kstar ζCfg theta B pstar hζCfg hθ hB hpstar
  refine ⟨min capCommon capDeep,lt_min hCommon hDeep,?_⟩
  intro ζ hζ hcap
  exact ⟨hCommonApply ζ hζ (hcap.trans (min_le_left _ _)),
    hDeepApply ζ hζ (hcap.trans (min_le_right _ _))⟩
end Oberwolfach
