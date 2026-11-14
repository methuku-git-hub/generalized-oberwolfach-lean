module

public import Oberwolfach.MarkedAbsorbableCorrectionNestedBalance
public import Oberwolfach.MarkedLongCommonProtectedCorrection
public import Oberwolfach.MarkedCommonCorrectionErrorChoices
public import Oberwolfach.MarkedProtectedCorrectionAbsorbable
public import Oberwolfach.MarkedLongCommonAgreementGlobalBalance
public import Oberwolfach.MarkedLongCommonAgreementInitialCuts
public import Oberwolfach.MarkedAdaptiveAgreementRobustAbsorber
public import Oberwolfach.VortexFirstPairProtectedSize

@[expose] public section
/-! Assemble the common event, protected correction and robust absorber on
one retained sample, with the correction threshold chosen first. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 50000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonCorrectionNestedFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem marked_long_common_event_correction_preserves_nested_balance
    (r:ℕ) (ρ₀ γRich kstar tstar ζRob εRob:ℝ)
    (hρ₀:0<ρ₀) (hγ:0<γRich) (hkstar:0<kstar)
    (htstar:0<tstar) (htstar1:tstar≤1) (hζRob:0<ζRob):
    ∃η₀:ℝ,0<η₀ ∧ ∃εRef εNbr:ℝ,0<εRef ∧ 0<εNbr ∧ ∃N:ℕ,∀(n:ℕ),N≤n→1≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hsize:ρ*Dnat=2*Fintype.card U)
    (hεQ:0≤εQ) (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (β βCommon εAbs δRef ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel:ℝ)
    (levelWeight:∀i,(Fin ((r+4)+1)→markedVortexVertexType Q i)→ℝ)
    (z:RawMarkedRetainedOutcome (U:=U) (Color:=Bool) π d false)
    (hEvent:
      let fV:=markedVortexVertexEmbedding Q
      let gV:=markedVortexHubEmbedding Q
      let ρi:=markedVortexPermutation Q π hpres
      let Aset:=markedVortexInnerVertices Q
      let Bset:=markedVortexInnerHubs Q
      let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
      let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
      let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i);
      MarkedAdaptiveAgreementProperty r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
        β βCommon εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
        (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
        P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight
        (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false z)
    (hpmin:kstar≤ρ*(1/100)/2) (hkmin:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2),
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false;
    MarkedProtectedAbsorbableCorrectionWithNestedBalance P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H
      (Q.extendedVertices 1) (Q.extendedIndices 1):=by
  let cuth:=min ((γRich/2)*kstar) tstar/128
  have hhcut:0<cuth:=by dsimp [cuth];positivity
  obtain ⟨η₀,hη₀,N,hN⟩:=marked_long_common_event_protected_absorbable_correction r ρ₀ γRich kstar tstar ζRob εRob
    hρ₀ hγ hkstar htstar htstar1 hζRob
  obtain ⟨εRef,εNbr,hεRef,hεNbr,_,_,_,hcutChoice,hbudgets⟩:=
    marked_common_correction_error_choices (r+4) cuth η₀ hhcut hη₀
  refine ⟨η₀,hη₀,εRef,εNbr,hεRef,hεNbr,N,?_⟩
  intro n hnN hn1 U _ _ _ P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs δRef ζ εBal ζBal ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight z hEvent hpmin hkmin H
  have hD0:(0:ℝ)≤Dnat:=Nat.cast_nonneg _
  have hhρ:=mul_nonneg (sub_nonneg.mpr hρhi) hD0
  have huR:(Fintype.card U:ℝ)≤n:=by nlinarith [hsize,hDhi]
  have hu:Fintype.card U≤n:=by exact_mod_cast huR
  obtain ⟨hbudget,hmarked,hcolumn⟩:=hbudgets n (Fintype.card U) hu
  have hresult:=hN n hnN hn1 U P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs εRef δRef ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight z hEvent hεNbr.le hpmin hkmin (hcutChoice hNbr) hbudget hmarked (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hcolumn)
  exact marked_absorbable_correction_preserves_nested_balance P π d r size aRob bRob eRob f₀ εRob ζRob z.1 H
    (Q.extendedVertices 1) (Q.extendedIndices 1) hresult
end Oberwolfach
