module

public import Oberwolfach.MarkedVortexCorrectedCompleteFromMatchingFieldsTwoScale
public import Oberwolfach.MarkedVortexCorrectedCompleteSeparateParentExplicitCapSplit

@[expose] public section
/-! The physical parent density used by the global correction cap is independent
of the inner density used by the vortex level geometry. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 60000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [Nonempty V] [DecidableEq U]
theorem marked_vortex_corrected_complete_from_matching_fields_explicit_local_cap
    (r k₀ d:ℕ)
    (α ρ₀ sstar tstar kstar:ℝ)
    (εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ)
    (G:SimpleGraph V)
    (D m:ℕ)
    (β ε:ℝ)
    (Q:Vortex U G D β ε m)
    (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ)
    (s₀ p kval:ℝ)
    (q:U → Γ → ℝ)
    (s:U → Color → ℝ)
    (a:Γ)
    (j:Color)
    (weightParent:∀i,(Fin (r+4+1) → markedVortexVertexType Q i) → ℝ)
    (weight:∀i,(Fin (r+4+1) → ↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i))) → ℝ)
    (σold σglobal:RawMarkedOutcome V U Γ Color)
    (Hold Hglobal:Bool → V → U → Prop)
    (βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut αParent κold xold thetaOld etaOld:ℝ)
    (N NI Kgeom:ℕ)
    (hα:0<α)
    (hαle:α ≤ αParent)
    (hκle:κold ≤ κ)
    (hxle:xold ≤ x)
    (hθle:thetaOld ≤ thetaDeep)
    (hηle:etaOld ≤ eta)
    (hρ:0  ≤  initialIndexDensity U D)
    (hs₀:0 ≤ s₀)
    (hd:1 ≤ d)
    (he:0 ≤ ε)
    (hp:p=initialIndexDensity U D*s₀/2)
    (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u a=s₀/(((r+4):ℕ):ℝ))
    (hs0:∀u,s u j=s₀)
    (hXi0:0 ≤ xiDeep)
    (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep ≤ κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep ≤ (s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i ≤ L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      τParent (successorWeightLower k₀ (αParent/4)) (successorWeightUpper k₀ (αParent/4)) (weightParent i))
    (hActiveWeight:∀i ≤ L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      τ (successorWeightLower k₀ (αParent/4)) (successorWeightUpper k₀ (αParent/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Color) π d a)
    (hraw:σold=z.1)
    (hspokes:Hold=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) a
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) a)) z.2 a j)
    (hGood:MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d αParent ρ₀ sstar tstar kstar
      εAbs ζAbs βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s a j weightParent weight z)
    (hβA:βA ≤ βCommon)
    (hζκ:ζCommon ≤ κold/4)
    (hC:3*βA ≤ markedLocalCycleCoefficient r (αParent/2) (tstar/2) kstar-(r+5:ℕ)*ζCfg)
    (hP:3*βA ≤ markedLocalPathCoefficient r (αParent/2) (tstar/2) kstar-(r+4:ℕ)*ζCfg)
    (hrec:βrec ≤ βA)
    (herr:tolRef+(r+12:ℕ)*ζActive ≤ κold/4)
    (hζActiveK:ζActive ≤ κold/4)
    (hεeq:εref ≤ κold/4)
    (hδeq:δref=κold)
    (hpot:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent ≤ κold/4)
    (hdeep:τParent+tolParent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*ζParent ≤ thetaOld/4)
    (hxold:0 ≤ xold)
    (hbal:epsBal+((r+4)+2:ℕ)*ζBal ≤ etaBal)
    (hmargin:epsBal+((r+4)+2:ℕ)*ζBal ≤ xold/2)
    (hterminal:L+1=Q.length)
    (hrowmargin:rowErr+ζRow ≤ (s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide ≤ etaOld/4)
    (hbquarter:β ≤ 1/4)
    (hh:0 ≤ hIcut)
    (hδα:deltaI ≤ (αParent/2)/32)
    (hδstar:deltaI ≤ kstar/32)
    (hδt:2*deltaI ≤ tstar/8)
    (hhstar:2*hIcut ≤ (αParent/2)*kstar/4)
    (hhs:2*hIcut ≤ tstar/8-ζCut)
    (hEndpoint:tolRef+(r+12:ℕ)*ζActive ≤ xold/2)
    (iota ζchange ζactive:ℝ)
    (hηBalPos:0<etaBal)
    (hxPos:0<x)
    (hiota:0 < iota)
    (hζchange:0 ≤ ζchange) (hζactive:0≤ζactive)
    (hepsBal:0 ≤ epsBal)
    (hζBal:0 ≤ ζBal)
    (hBalRelative:epsBal+((r+4)+2:ℕ)*ζBal ≤ etaBal/2)
    (hBalAmbient:epsBal+((r+4)+2:ℕ)*ζBal ≤ x/4)
    (FR:SimpleGraph V)
    (FS:SimpleGraph (V⊕U))
    (hsize:iota*Fintype.card (markedVortexVertexType Q 0) ≤ ((markedVortexInnerVertices Q 0).card:ℝ))
    (hn:0<Fintype.card V)
    (hu:Fintype.card U ≤ Fintype.card V)
    (pstar:ℝ)
    (hpstar:0<pstar)
    (hplo:pstar ≤ p)
    (hklo:pstar ≤ kval)
    (hslo:pstar ≤ s₀)
    (hp1:p ≤ 1)
    (hk1:kval ≤ 1)
    (hs1:s₀ ≤ 1)
    (hDlo:(Fintype.card (markedVortexVertexType Q 0):ℝ)/2 ≤ 2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D)
    (hDhi:2*(Fintype.card (markedVortexHubType Q 0):ℝ)/initialIndexDensity U D ≤ 2*Fintype.card (markedVortexVertexType Q 0))
    (Hordinary:V → U → Prop)
    (hboundaryHalf:xold ≤ x/2)
    (hκPos:0<κ)
    (ωParent:ℝ) (hωPos:0<ωParent)
    (plo klo:ℝ)
    (hploPos:0<plo)
    (hkloPos:0<klo)
    (hαeq:αParent=2*α)
    (hκoldEq:κold=κ/2)
    (hUlower:ωParent*Fintype.card V ≤ (Fintype.card U:ℝ))
    (hpLower:plo ≤ p)
    (hkLower:klo ≤ kval)
    (ζFixed:ℝ)
    (hζFixed:0<ζFixed)
    (hCfg:2*ζCfg ≤ ζFixed)
    (hθDeepPos:0<thetaDeep)
    (hθoldHalf:thetaOld ≤ thetaDeep/2)
    (hcycleDeep:3*βA ≤ markedLocalCycleCoefficient r (αParent/2) (tstar/2) kstar-(r+5:ℕ)*ζFixed)
    (hpathDeep:3*βA ≤ markedLocalPathCoefficient r (αParent/2) (tstar/2) kstar-(r+4:ℕ)*ζFixed)
    (hηPos:0<eta)
    (htstarPos:0<tstar)
    (FSactive:SimpleGraph (↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1))⊕markedVortexNonDeeperHubType Q 0))
    (hnactive:0<Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)))
    (hβrect:βrec ≤ (s₀/((r+4:ℕ):ℝ))/4)
    (htt:tstar ≤ s₀/((r+4:ℕ):ℝ))
    (hactiveErr:τ+tolLocal+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (αParent/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*ζWide ≤ eta/8)
    (hactiveRow:rowErr+ζRow ≤ tstar/16)
    (hDactiveLo:(Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)):ℝ)/2 ≤ 
      2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D)
    (hDactiveHi:2*((((Finset.univ\markedVortexInnerHubs Q 1):Finset (markedVortexHubType Q 1)).card):ℝ)/initialIndexDensity U D ≤ 
      2*Fintype.card ↥((Finset.univ\markedVortexInnerVertices Q 1):Finset (markedVortexVertexType Q 1)))
    (hρ₀Pos:0<ρ₀)
    (hρlo:ρ₀ ≤ initialIndexDensity U D)
    (hρhi:initialIndexDensity U D ≤ 1)
    (htstarCap:tstar ≤ (1/100)/(((r+4):ℕ):ℝ))
    (hkstarPos:0<kstar)
    (hkstarCap:kstar ≤ initialIndexDensity U D*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hs₀Eq:s₀=(1/100:ℝ))
    (cLocal:ℝ)
    (hζactiveCap:ζactive≤Classical.choose (marked_vortex_active_transfer_from_parent_fixed_margin r αParent tstar kstar ζFixed eta
      (successorWeightUpper k₀ (αParent/4)) pstar hζFixed hηPos
      (successorWeightConstants_pos k₀ (αParent/4) (by have hh:=lt_of_lt_of_le hα hαle;positivity)).2.le hpstar htstarPos))
    (hcLocalEq:cLocal=markedExplicitJointLocalCap (r+4) (r+12) etaBal x)
    (hζFinal:ζchange ≤ Classical.choose (marked_vortex_fixed_margin_local_correction_cap r κ αParent ωParent plo klo tstar kstar ζFixed thetaDeep (1:ℝ)
      (successorWeightUpper k₀ (αParent/4)) pstar (1:ℝ) (1:ℝ) (1:ℝ)
      hκPos (lt_of_lt_of_le hα hαle) hωPos hploPos hkloPos htstarPos hζFixed hθDeepPos (by norm_num)
      (successorWeightConstants_pos k₀ (αParent/4) (by have hh:=lt_of_lt_of_le hα hαle;positivity)).2.le
      hpstar (by norm_num) (by norm_num) (by norm_num)))
    (hData:MarkedVortexPhysicalCorrectionFieldsTwoScale G D m β ε Q π d a j z σold σglobal Hold Hglobal Hordinary FR FS FSactive ζchange ζactive cLocal)
:
  ∀ gammaLoss sigmaLoss:ℝ,
    (∀rho omega t:ℝ,ρ₀ ≤ rho → rho ≤ 1 → ρ₀/8 ≤ omega → omega ≤ 1 → tstar ≤ t → (r+4:ℝ)*t ≤ 1 → 
      ρ₀/400 ≤ rho*(r+4:ℝ)*t/2 → kstar ≤ rho*(r+4:ℝ)*t/2 → kstar ≤ rho*t/2 → kstar ≤ t → 
      ∀(Gamma Shade:Type) [Fintype Gamma] [Fintype Shade],
      ∀level:MarkedReferenceLevelData Gamma Shade r d N NI Kgeom (α/16) rho omega t kstar βA
        (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        κ ξ thetaDeep (α/8) ω (ε/4) βrec (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        eta x (ρ₀/16) hIcut deltaI etaBal,
      MarkedReferenceLevelStepProperty level gammaLoss sigmaLoss) → 
    ∀ sizeAbs aAbs bAbs eAbs fAbs:ℕ,∀ εabs:ℝ,
    let E:=MarkedSampleArc G π (3*d) (fun e=>σglobal (Sum.inl e)) false
    let K:=MarkedSampleArc G π (3*d) (fun e=>σglobal (Sum.inl e)) true
    let S:=Finset.univ.filter (fun z:V×U=>Hglobal false z.1 z.2∨Hglobal true z.1 z.2);
    MarkedRemainderDivisible (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hglobal true) Finset.univ S (r+4) → 
    MarkedReservedTerminalAbsorberProperty (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (Hglobal false) (Hglobal true) π (3*d) r sizeAbs aAbs bAbs eAbs fAbs εabs → 
    G.IsRegularOfDegree D → 0<D → ε≤εabs → 2*m≤sizeAbs →
    ∀(hγ:0<gammaLoss) (hσ:0<sigmaLoss),
    let NB:=Classical.choose (marked_vortex_terminal_budget eAbs gammaLoss sigmaLoss hγ hσ);
    NB≤Fintype.card V →
    HasResourceDecomposition (fun W:MarkedWheel (fun e:E=>e.val.1) (fun e=>e.val.2)
      (fun e:K=>e.val.1) (fun e=>e.val.2) (r+4) π (3*d) (Hglobal false) (Hglobal true)=>markedWheelPhysicalResources W)
      (markedDecompositionTarget (markedPhysicalRimSet (fun e:E=>e.val.1) (fun e=>e.val.2)
        (fun e:K=>e.val.1) (fun e=>e.val.2) π) (Hglobal false) (Hglobal true)) :=by
  have hApplied:=marked_vortex_corrected_complete_from_separate_parent_explicit_cap_split
    r k₀ d α ρ₀ sstar tstar kstar εAbs ζAbs
    βconfig βCommon εref δref tolRef ζActive τ tolLocal ζLocal τParent
    tolParent ζParent epsBal ζBal ζCut ζCfg rowErr ζCommon ζWide ζRow
    size a₀ b₀ e₀ f₀ G D m β ε
    Q π hpres L s₀ p kval q s a
    j weightParent weight σold σglobal Hold Hglobal hData.htypes hData.hsep βA
    βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI
    hIcut αParent κold xold thetaOld etaOld N NI Kgeom hα
    hαle hκle hxle hθle hηle hρ hs₀ hd he hp
    hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo z
    hraw hspokes hGood hβA hζκ hC hP hrec herr hζActiveK
    hεeq hδeq hpot hdeep hxold hbal hmargin hterminal hrowmargin hloadmargin
    hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint iota ζchange ζactive
    hηBalPos hxPos hiota hζchange hζactive hepsBal hζBal hBalRelative hBalAmbient FR FS
    hData.hinterval hData.hR hData.hS hData.hFR hData.hFS hsize hn hu pstar hpstar
    hplo hklo hslo hp1 hk1 hs1 hDlo hDhi Hordinary hData.hHglobal
    hData.hrawInner hData.hOrdinary hboundaryHalf hκPos ωParent hωPos plo klo hploPos hkloPos hαeq
    hκoldEq hUlower hpLower hkLower ζFixed hζFixed hCfg hθDeepPos hθoldHalf hcycleDeep
    hpathDeep hηPos htstarPos FSactive hData.hSactive hData.hFSactive hnactive hβrect htt hactiveErr
    hactiveRow hDactiveLo hDactiveHi hρ₀Pos hρlo hρhi htstarCap hkstarPos hkstarCap hs₀Eq
    hζactiveCap cLocal hcLocalEq hData.hLocalRimOutside hData.hLocalSpokeOutside hData.hPhysicalNoNew hData.hPhysicalLoss hζFinal
  exact hApplied
end Oberwolfach
