module

public import Oberwolfach.LongTerminalPreparedChainProbability
public import Oberwolfach.LongTerminalProtectedSelectedEncodedSplitLoad
public import Oberwolfach.LongEveryReserveConcreteClassEvent
public import Oberwolfach.LongEveryReservePreparedClassesEvent
public import Oberwolfach.LongPreparedSelectorCommonProbability
public import Oberwolfach.LongEveryClassValidDeletionEvent
public import Oberwolfach.LongEveryClassMatchingResult
public import Oberwolfach.LongReservedOrientationRetainedMatchingResult
public import Oberwolfach.LongReservedResultRetainsAbsorberRims
public import Oberwolfach.LongReservedOrientationMatchingResult
public import Oberwolfach.LongValidDeletionOrientationResultReserved
public import Oberwolfach.MarkedFixedWeightsActualSampleDensityProbability
public import Oberwolfach.FiniteLawSupportProbabilityMono

@[expose] public section
/-! A pointwise density decomposition at each supported sample preserves
any probability bound for the same fixed parent and active weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 100000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance namedTerminalPreparedProbabilityFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _
variable {n:ℕ} {U:Type} [Fintype U] [Nonempty (Fin n)] [DecidableEq U]
local notation "V" => Fin n
theorem marked_named_parent_terminal_prepared_probability
    (r k₀ d:ℕ) (α ρ₀ sstar tstar kstar:ℝ)
    (εAbsP ζAbsP βconfigP βCommonP εRef κ δparent εBal ζBal:ℝ)
    (size a₀ b₀ e₀ f₀:ℕ) (G:SimpleGraph V) (D m:ℕ) (β ε:ℝ)
    (Q:Vortex U G D β ε m) (π:Equiv.Perm V)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (L:ℕ) (s₀ p kval:ℝ) (q:U→Bool→ℝ) (s:U→Bool→ℝ)
    (weightParent:∀i,(Fin (r+4+1)→markedVortexVertexType Q i)→ℝ)
    (weight:∀i,(Fin (r+4+1)→↥((Finset.univ\markedVortexInnerVertices Q i):Finset (markedVortexVertexType Q i)))→ℝ)
    (βA βrec ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut:ℝ) (N NI Kgeom:ℕ)
    (hd:1≤d) (he:0≤ε)
    (hp:p=initialIndexDensity U D*s₀/2) (hk:kval=p/(((r+4):ℕ):ℝ))
    (hq0:∀u,q u false=s₀/(((r+4):ℕ):ℝ)) (hs0:∀u,s u false=s₀)
    (hXi0:0≤xiDeep) (hXiScale:(4*Kgeom+3*r+50:ℝ)*xiDeep≤κ/2)
    (hDeepGap:(1+2/initialIndexDensity U D)*xiDeep≤(s₀/(((r+4):ℕ):ℝ))*ω/32)
    (hParentWeight:∀i≤L,SuccessorSequenceWeightConditions (G.comap (markedVortexVertexEmbedding Q i))
      (markedVortexPermutation Q π hpres i) (3*d) (2*(Fintype.card (markedVortexHubType Q i):ℝ)/initialIndexDensity U D)
      δparent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weightParent i))
    (hActiveWeight:∀i≤L+1,SuccessorSequenceWeightConditions (G.comap (markedVortexActiveVertexEmbedding Q i))
      (markedVortexActivePermutation Q π hpres i) (3*d)
      (2*((((Finset.univ\markedVortexInnerHubs Q i):Finset (markedVortexHubType Q i)).card):ℝ)/initialIndexDensity U D)
      δparent (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4)) (weight i))
    (hGeo:MarkedVortexGeometricRecordEvent Q α ρ₀ κ hIcut ξ xiDeep ω x N NI L)
    (hβA:βA≤βCommonP) (hζκ:δparent≤κ/4)
    (hC:3*βA≤markedLocalCycleCoefficient r (α/2) (tstar/2) kstar-(r+5:ℕ)*δparent)
    (hP:3*βA≤markedLocalPathCoefficient r (α/2) (tstar/2) kstar-(r+4:ℕ)*δparent)
    (hrec:βrec≤βA) (herr:δparent+(r+12:ℕ)*δparent≤κ/4) (hζActiveK:δparent≤κ/4)
    (hεeq:εRef≤κ/4)
    (hpot:δparent+δparent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δparent≤κ/4)
    (hdeep:δparent+δparent+11*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*δparent≤thetaDeep/4)
    (hx:0≤x) (hbal:εBal+((r+4)+2:ℕ)*ζBal≤etaBal)
    (hmargin:εBal+((r+4)+2:ℕ)*ζBal≤x/2) (hterminal:L+1=Q.length)
    (hrowmargin:δparent+δparent≤(s₀/((r+4:ℕ):ℝ))/8)
    (hloadmargin:δparent+δparent+5*(((r+4:ℕ):ℝ)+1)^4*(2*successorWeightUpper k₀ (α/4)/(ρ₀*sstar/(2*((r+4:ℕ):ℝ)))^(2*(r+4)+1))*(4/ε)*δparent≤eta/4)
    (hbquarter:β≤1/4) (hh:0≤hIcut) (hδα:deltaI≤(α/2)/32) (hδstar:deltaI≤kstar/32)
    (hδt:2*deltaI≤tstar/8) (hhstar:2*hIcut≤(α/2)*kstar/4) (hhs:2*hIcut≤tstar/8-δparent)
    (hEndpoint:δparent+(r+12:ℕ)*δparent≤x/2)
    (sizeCorr aCorr bCorr eCorr fCorr:ℕ) (gammaLoss sigmaLoss ξCorr εCorr ζCorr:ℝ) (hξCorr:0≤ξCorr)
    (hbudget:6*(8*((((r+4):ℕ):ℝ)+1)*ξCorr*Fintype.card V)≤
      min (gammaLoss*Fintype.card V) (sigmaLoss*Fintype.card V))
    (hreg:G.IsRegularOfDegree D) (hD:0<D) (hρhi:initialIndexDensity U D≤1)
    (heCorr:ε≤εCorr) (hsizeCorr:2*m≤sizeCorr)
    (extra:ℝ)
    (μ:FiniteLaw (MarkedExpandedActualOutcome (U:=U) π d))
    (Other:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (Tail:MarkedExpandedActualOutcome (U:=U) π d→Prop)
    (ζEarly ξClass:ℝ) (Kmix:ℕ) (θ alphaMatch γMatch epsMatch βList:ℝ)
    (F:U→SimpleGraph V) (hF:∀u,(F u).IsRegularOfDegree 2)
    (seedWeight:(Fin (r+4+1)→V)→ℝ)
    (wSeed:∀i:Fin Kmix,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ)
    (hρ₀pos:0<ρ₀) (hρlo:ρ₀≤ initialIndexDensity U D)
    (htstarpos:0<tstar) (htstarcap:tstar≤(1/100)/(((r+4):ℕ):ℝ))
    (hkstarpos:0<kstar) (hkstarcap:kstar≤ initialIndexDensity U D*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hs₀:s₀=(1/100:ℝ))
    (hSteps:∀rho omega t:ℝ,ρ₀≤rho → rho≤1 → ρ₀/8≤omega → omega≤1 → tstar≤t → (r+4:ℝ)*t≤1 →
      ρ₀/400≤rho*(r+4:ℝ)*t/2 → kstar≤rho*(r+4:ℝ)*t/2 → kstar≤rho*t/2 → kstar≤t →
      ∀(Gamma Color:Type) [Fintype Gamma] [Fintype Color],
      ∀ level:MarkedReferenceLevelData Gamma Color r d N NI Kgeom (α/16) rho omega t kstar βA
        (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        κ ξ thetaDeep (α/8) ω (ε/4) βrec (successorWeightLower k₀ (α/4)) (successorWeightUpper k₀ (α/4))
        eta x (ρ₀/16) hIcut deltaI etaBal,
        MarkedReferenceLevelStepProperty level (gammaLoss+extra) (sigmaLoss+extra))
    (Bpart:ℕ) (hReserveCap:eCorr≤Bpart) (heCorrSize:(eCorr:ℝ)≤extra*n)
    (lamAssign δlocal δglobal αMatchPrep bmatch ξPrep BMref:ℝ)
    (BOref:Fin Kmix→ℝ) (ξSeed ΔSeed ζret ζselect terr τerr:ℝ)
    (hPrepared:∀sample:MarkedExpandedActualOutcome (U:=U) π d,
      FirstVortexConcreteBoundaryEvent G π d r D m β ε Q θ ρ₀ BMref BOref F hF seedWeight wSeed
        alphaMatch γMatch epsMatch ζEarly ξSeed ΔSeed ζret ζselect βList terr τerr sample (Q.extendedVertices 1)→
      ∀(D₀:MarkedReferenceDeletion G π d (fun e=>rawExpandedMarkedCollapse e (sample.1 e)))
        (C:Finset (Finset V⊕(V×U))),
      LongEveryClassMatchingResult ζEarly G π d r gammaLoss sigmaLoss ξClass sample (Q.extendedVertices 1)
        Kmix θ D alphaMatch γMatch epsMatch βList F hF seedWeight wSeed D₀ C→
      LongBoundaryPreparedClasses G π d r D m β ε Q sample θ alphaMatch γMatch epsMatch βList ξClass ζEarly
        lamAssign δlocal δglobal αMatchPrep bmatch ρ₀ ξPrep F hF seedWeight wSeed D₀ C):
    let Other':=fun sample:MarkedExpandedActualOutcome (U:=U) π d=>
      ((Other sample ∧ FirstVortexConcreteBoundaryEvent G π d r D m β ε Q θ ρ₀ BMref BOref F hF seedWeight wSeed
        alphaMatch γMatch epsMatch ζEarly ξSeed ΔSeed ζret ζselect βList terr τerr sample (Q.extendedVertices 1)) ∧
      LongEveryReservePreparedClassesEvent G π d r D m β ε Q Bpart gammaLoss sigmaLoss ξClass ζEarly sample
        θ alphaMatch γMatch epsMatch βList lamAssign δlocal δglobal αMatchPrep bmatch ρ₀ ξPrep F hF seedWeight wSeed) ∧
      LongEveryReserveConcreteClassEvent G π d r D m β ε Q Bpart gammaLoss sigmaLoss ξClass ζEarly
        sample θ (D:ℝ) alphaMatch γMatch epsMatch βList F hF seedWeight wSeed
    let Common:=fun sample:MarkedExpandedActualOutcome (U:=U) π d=>Tail sample ∧
      LongEveryClassValidDeletionEvent ζEarly G π d r gammaLoss sigmaLoss ξClass sample
        (Q.extendedVertices 1) (Q.extendedIndices 1) Kmix eCorr θ (D:ℝ) alphaMatch γMatch epsMatch βList F hF seedWeight wSeed;
    let ParentEvt:=fun sample:MarkedExpandedActualOutcome (U:=U) π d=>(MarkedVortexParentRecordSmallerReferenceEvent r (r+12) k₀ d α ρ₀ sstar tstar kstar
      εAbsP ζAbsP βconfigP βCommonP εRef κ δparent δparent δparent δparent δparent δparent δparent δparent εBal ζBal δparent δparent δparent δparent δparent δparent
      size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s false false weightParent weight (markedExpandedActualSelected π d sample))
    let CorrectionEvt:=fun sample:MarkedExpandedActualOutcome (U:=U) π d=>(MarkedProtectedAbsorbableCorrectionWithBounds G π d r sizeCorr aCorr bCorr eCorr fCorr εCorr ζCorr ξCorr (markedExpandedActualSelected π d sample).1
      (retainedRawMarkedSpokes π d (fun e=>(markedExpandedActualSelected π d sample).1 (Sum.inr e)) false (startRetentionMinimum (rawStartHubSet π d (fun e=>(markedExpandedActualSelected π d sample).1 (Sum.inr e)) false)) (markedExpandedActualSelected π d sample).2 false false)
      (Q.extendedVertices 1) (Q.extendedIndices 1))
    let Boundary:=fun sample:MarkedExpandedActualOutcome (U:=U) π d=>
      FirstVortexConcreteBoundaryEvent G π d r D m β ε Q θ ρ₀ BMref BOref F hF seedWeight wSeed
        alphaMatch γMatch epsMatch ζEarly ξSeed ΔSeed ζret ζselect βList terr τerr sample (Q.extendedVertices 1);
    ∀b:ℝ,b≤μ.probability (fun sample=>Other sample ∧ ParentEvt sample ∧ Tail sample ∧ CorrectionEvt sample ∧
      LongEveryClassValidDeletionEvent ζEarly G π d r gammaLoss sigmaLoss ξClass sample
        (Q.extendedVertices 1) (Q.extendedIndices 1) Kmix Bpart θ D alphaMatch γMatch epsMatch βList F hF seedWeight wSeed ∧
      LongEveryReserveConcreteClassEvent G π d r D m β ε Q Bpart gammaLoss sigmaLoss ξClass ζEarly sample
        θ D alphaMatch γMatch epsMatch βList F hF seedWeight wSeed ∧ Boundary sample)→b≤μ.probability (fun sample=>
      Other' sample ∧ Common sample ∧ ParentEvt sample ∧ CorrectionEvt sample ∧
      LongTerminalPreparedChainEvent G π d r D m β ε Q gammaLoss sigmaLoss ξClass ζEarly eCorr L sample
        θ alphaMatch γMatch epsMatch βList lamAssign δlocal δglobal αMatchPrep bmatch ρ₀ ξPrep F hF seedWeight wSeed
        (fun _ _ _=>True)) := by
  intro Other' Common ParentEvt CorrectionEvt Boundary b hcore
  have hb:=long_prepared_selector_common_probability G π d r D m β ε Q eCorr Bpart hReserveCap
    gammaLoss sigmaLoss ξClass ζEarly θ alphaMatch γMatch epsMatch βList lamAssign δlocal δglobal αMatchPrep bmatch ρ₀ ξPrep BMref
    BOref ξSeed ΔSeed ζret ζselect terr τerr F hF seedWeight wSeed
    (by
      intro sample hboundary D₀ C hmatch
      exact hPrepared sample hboundary D₀ C hmatch) μ Other ParentEvt Tail CorrectionEvt b hcore
  apply hb.trans
  apply finiteLaw_probability_mono_on_support
  intro sample hpos hBase
  obtain ⟨outcome,hMass,hProps,hGood,hChain,DA,DS,D₀,hDA,hDS,hValid,hAvoid,hMix,T₀,hT₀,hRemoved,hRemain,hAbs,hReserve⟩:=
    marked_fixed_weights_actual_sample_density_decomposition r k₀ d α ρ₀ sstar tstar kstar
    εAbsP ζAbsP βconfigP βCommonP εRef κ δparent δparent δparent δparent δparent δparent δparent δparent εBal ζBal δparent δparent δparent δparent δparent δparent
    size a₀ b₀ e₀ f₀ G D m β ε Q π hpres L s₀ p kval q s weightParent weight
    βA βrec κ ξ thetaDeep ω xiDeep etaBal x eta deltaI hIcut N NI Kgeom hd he hp hk hq0 hs0 hXi0 hXiScale hDeepGap hParentWeight hActiveWeight hGeo
    hβA hζκ hC hP hrec herr hζActiveK hεeq (by rfl) hpot hdeep hx hbal hmargin hterminal hrowmargin hloadmargin hbquarter hh hδα hδstar hδt hhstar hhs hEndpoint
    sizeCorr aCorr bCorr eCorr fCorr gammaLoss sigmaLoss ξCorr εCorr ζCorr hξCorr hbudget hreg hD hρhi heCorr hsizeCorr extra μ.mass Other' Common sample
    ⟨hpos,by rcases hBase with ⟨hprior,hconcrete,hparent,hcommon,hcorr⟩; exact ⟨⟨hprior,hconcrete⟩,hparent,hcommon,hcorr⟩⟩ hρ₀pos hρlo htstarpos htstarcap hkstarpos hkstarcap hs₀ hSteps
  subst DA
  subst DS
  obtain ⟨⟨⟨hOther,hEq⟩,hCommon⟩,hCorr⟩:=hProps
  subst sample
  have hSize:(eCorr:ℝ)≤extra*Fintype.card V:=by simpa only [Fintype.card_fin] using heCorrSize
  obtain ⟨C,hFReserve,hCe,hCr,hCu,hfixed,horiginal,D₂,h₂,havoid,hremoved,hremain,hdis,T,hT,hTremoved,hTremain,hdec⟩:=hReserve ∅ (by simp) hSize
  have hPreparedEvent:=hOther.1.2
  have hPrepared:=hPreparedEvent D₀
    (by simpa only [markedExpandedActualSelected,rawExpandedMarkedCollapse,id_eq,Fintype.card_fin] using hValid)
    C (hCe.trans hReserveCap) hdis
  have hTerm:longTerminalProtectedReserve G π d r outcome outcome.2 (Q.extendedVertices 1) (Q.extendedIndices 1)
      gammaLoss sigmaLoss eCorr (Q.extendedVertices (L+1)) (Q.extendedIndices (L+1)) D₀ C.edges :=by
    dsimp only [longTerminalProtectedReserve]
    refine ⟨?_,hCe,hdis,?_⟩
    · simpa only [markedExpandedActualSelected,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id_eq,Fintype.card_fin] using hValid
    · simpa only [markedExpandedActualSelected,rawExpandedApproximateCollapse,rawExpandedMarkedCollapse,id_eq] using horiginal
  refine ⟨hOther,hCommon,hGood,hCorr,?_⟩
  exact ⟨D₀,C.edges,hTerm,hPrepared,True.intro⟩
end Oberwolfach
