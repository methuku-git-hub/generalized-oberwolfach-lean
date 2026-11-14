module

public import Oberwolfach.MarkedVortexInitialDeepFieldsTransfer
public import Oberwolfach.MarkedVortexSmallerParentToRecordConsequences
public import Oberwolfach.MarkedVortexCorrectedRecordConsequences

@[expose] public section
/-! Use the selected parent's more precise weighted load with its stronger
configuration event on the same sample before physical correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_vortex_initial_deep_from_selected_parent
    (r:ℕ) (αCfg tstar kstar ζCfg theta B pstar:ℝ)
    (hζCfg:0<ζCfg) (hθ:0<theta) (hB:0≤B) (hpstar:0<pstar):
    ∃cap:ℝ,0<cap ∧ ∀ζ:ℝ,0≤ζ→ζ≤cap→
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
      (markedLocalCycleCoefficient r αCfg (tstar/2) kstar-(r+5:ℕ)*(ζCfg/2))
      (markedLocalPathCoefficient r αCfg (tstar/2) kstar-(r+4:ℕ)*(ζCfg/2)) σ H→
    MarkedLocalConfigurationsWithSpokes r P ρ d Finset.univ
      (3*min βA (t/4)) (3*min βA (t/4)) σ' H' ∧
    MarkedLocalSpokeLoadsWithSpokes P ρ d (r+4) Dload p kval s₀ (weightParent 0) (theta/4) σ' H' :=by
  obtain ⟨cap,hcap,htransfer⟩:=marked_vortex_initial_deep_fields_transfer r αCfg tstar kstar ζCfg theta B pstar hζCfg hθ hB hpstar
  refine ⟨cap,hcap,?_⟩
  intro ζ hζ hζcap V U Γ Color _ _ _ _ _ _ _ h k₀ d α ρ₀ sstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfgOld rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold σglobal Hold Hglobal
    βA βrec κ thetaOld etaBal x eta deltaI hIcut A hpEq hkEq htheta z hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq hpot hdeep hx hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint FR FS hn hinterval hR hS hFR hFS htypes
    W Z f g ρ P σ σ' H H' c t Dload hcycle hpath hDlo hDhi hp hk hs hp1 hk1 hs1 hw hcfg
  have hOld':=marked_vortex_smaller_parent_to_record_consequences r h k₀ d α ρ₀ sstar tstar kstar
    εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfgOld rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z hGood
    βA βrec κ hβA hζκ hC hP hrec herr hζActiveK hεeq hδeq thetaOld hpot hdeep etaBal x hx hbal hmargin hterminal eta hrowmargin hloadmargin deltaI hIcut hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
  have hOld:MarkedVortexCorrectedRecordConsequences r h k₀ d α ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfgOld rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight σold Hold βA βrec κ thetaOld etaBal x eta deltaI hIcut :=by
    rw [hraw,hspokes]
    exact hOld'
  have hc:(c:ℝ)≠0:=by dsimp [c];positivity
  have hct:c*t=s₀:=by dsimp [t];field_simp
  have hct':(r+4:ℝ)*t=s₀:=by simpa only [c,Nat.cast_add,Nat.cast_ofNat] using hct
  have hpRef:initialIndexDensity U D*(r+4:ℝ)*t/2=p:=by rw [hpEq,←hct];dsimp [c];push_cast;ring
  have hkRef:(initialIndexDensity U D*(r+4:ℝ)*t/2)/(r+4:ℝ)=kval:=by rw [hpRef,hkEq];norm_cast
  unfold MarkedVortexCorrectedRecordConsequences at hOld
  obtain ⟨_,_,_,hdeep,_,_,_,_⟩:=hOld
  obtain ⟨hload,_⟩:=hdeep 0 (Nat.zero_le L)
  have hh:=htransfer ζ hζ hζcap V U Γ Color G D m β ε Q π hpres d σold σglobal Hold Hglobal FR FS
    hn hinterval hR hS hFR hFS htypes (initialIndexDensity U D) t τParent A (thetaOld/4) βA (weightParent 0)
    hcycle hpath (by linarith) hDlo hDhi
    (by rw [hpRef];exact hp) (by rw [hkRef];exact hk) (by rw [hct'];exact hs)
    (by rw [hpRef];exact hp1) (by rw [hkRef];exact hk1) (by rw [hct'];exact hs1)
  rw [hpRef] at hh
  simp only [Nat.cast_add,Nat.cast_ofNat] at hkEq
  rw [←hkEq,hct'] at hh
  exact hh hw hcfg hload
end Oberwolfach
