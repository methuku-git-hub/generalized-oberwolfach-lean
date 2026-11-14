module

public import Oberwolfach.MarkedProtectedCorrectionWithBounds
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
local instance commonCorrectionWithBoundsFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem marked_long_common_event_protected_correction_with_bounds
    (r:ℕ) (ρ₀ γRich kstar tstar ζRob εRob:ℝ)
    (hρ₀:0<ρ₀) (hγ:0<γRich) (hkstar:0<kstar)
    (htstar:0<tstar) (htstar1:tstar≤1) (hζRob:0<ζRob):
    ∃ξCorr:ℝ,0<ξCorr ∧ 16*(((r+4:ℕ):ℝ)+1)*ξCorr≤ζRob ∧ ∃η₀:ℝ,0<η₀ ∧ ∃N:ℕ,∀(n:ℕ),N≤n→1≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρlo:ρ₀≤ρ) (hρhi:ρ≤1)
    (hDlo:(n:ℝ)/2≤Dnat) (hDhi:(Dnat:ℝ)≤2*n) (hsize:ρ*Dnat=2*Fintype.card U)
    (hεQ:0≤εQ) (hεQsmall:εQ≤min ((γRich/2)*kstar) tstar/128)
    (β βCommon εAbs εRef δRef ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel:ℝ)
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
    (hεNbr:0≤εNbr)
    (hpmin:kstar≤ρ*(1/100)/2) (hkmin:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hcutBudget:εNbr/(2*((hNbr:ℝ)+1))≤14*(min ((γRich/2)*kstar) tstar/128))
    (hbudget:2*(εRef*n)+2*(εNbr*Fintype.card U)≤η₀*n)
    (hmarked:εRef*n+εNbr*Fintype.card U≤η₀*n)
    (hcolumn:((((r+4):ℕ):ℝ)+1)*(εNbr*n)≤η₀*n),
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false;
    MarkedProtectedAbsorbableCorrectionWithBounds P π d r size aRob bRob eRob f₀ εRob ζRob ξCorr z.1 H
      (Q.extendedVertices 1) (Q.extendedIndices 1):=by
  let cutδ:=min (min (γRich/2) kstar) tstar/256
  let cuth:=min ((γRich/2)*kstar) tstar/128
  have hδ:0<cutδ:=by dsimp [cutδ];positivity
  have hδsmall:cutδ<1/4:=by
    have hh:=min_le_right (min (γRich/2) kstar) tstar
    dsimp [cutδ];linarith
  have hhcut:0<cuth:=by dsimp [cuth];positivity
  obtain ⟨ξCorr,hξCorr,hξscale,η₀,hη₀,N,hcor⟩:=marked_protected_canonical_correction_absorber_with_scale
    (r+4) r (by omega) rfl εRob (ρ₀/4) cuth cutδ ζRob (by positivity) hhcut hδ hδsmall hζRob
  refine ⟨ξCorr,hξCorr,hξscale,η₀,hη₀,max N 1,?_⟩
  intro n hnN hn1 U _ _ _ P π Dnat vsize βQ εQ Q hpres K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρlo hρhi hDlo hDhi hsize hεQ hεQsmall β βCommon εAbs εRef δRef ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig sstar τLevel levelWeight z hEvent hεNbr hpmin hkmin hcutBudget hbudget hmarked hcolumn H
  have hn:N≤Fintype.card (Fin n):=by simp only [Fintype.card_fin];omega
  have hnpos:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hρ:0<ρ:=hρ₀.trans_le hρlo
  have hDreal:0<(Dnat:ℝ):=lt_of_lt_of_le (by positivity) hDlo
  have hDnat:0<Dnat:=by exact_mod_cast hDreal
  have hωn:(ρ₀/4)*Fintype.card (Fin n)≤(Fintype.card U:ℝ):=by
    simp only [Fintype.card_fin]
    have hhρ:=mul_nonneg (sub_nonneg.mpr hρlo) hDreal.le
    have hhD:=mul_nonneg hρ₀.le (sub_nonneg.mpr hDlo)
    nlinarith [hsize]
  have hun:Fintype.card U≤Fintype.card (Fin n):=by
    simp only [Fintype.card_fin]
    have hhρ:=mul_nonneg (sub_nonneg.mpr hρhi) hDreal.le
    have hu:(Fintype.card U:ℝ)≤n:=by nlinarith [hsize,hDhi]
    exact_mod_cast hu
  have hpair:=vortex_first_pair_protected_size Q hεQ cuth hεQsmall
  have hH:∀v u,¬(H false v u∧H true v u):=by
    intro v u
    exact retainedMarkedSpokes_disjoint π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false v u
  have hrob:=marked_adaptive_agreement_robust_reserved_absorber r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
    (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
    P π (markedVortexVertexEmbedding Q) (markedVortexHubEmbedding Q) (markedVortexPermutation Q π hpres)
    (markedVortexInnerVertices Q) (markedVortexInnerHubs Q) (fun i=>Fintype.card (markedVortexVertexType Q i))
    (fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ) (fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ)
    (fun i=>Function.Embedding.refl (markedVortexHubType Q i)) levelWeight
    (longAssignedIntervalProbability F hF K (r+4) θ) (longAssignedSpokeProbability F hF K (r+4) θ) false false z hEvent
  have hbalance:=marked_long_common_agreement_initial_global_balance hn1 P π Dnat vsize βQ εQ Q hpres r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρ hsize
    β βCommon εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel η₀ hγ.le levelWeight z hEvent hbudget hmarked hcolumn
  have hcuts:=marked_long_common_agreement_initial_four_cuts hn1 P π Dnat vsize βQ εQ Q hpres r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρ hDnat hsize
    β βCommon εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel η₀ hγ levelWeight z hEvent hkstar htstar htstar1 hεNbr hpmin hkmin hcutBudget
  have hbw:∀u,|(∑v,if H false v u then (1:ℝ) else 0)-((r:ℝ)+4)*(∑v,if H true v u then (1:ℝ) else 0)|≤η₀*Fintype.card (Fin n):=by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using hbalance.2.2.2
  exact hcor size aRob bRob eRob f₀ η₀ hη₀.le le_rfl (Fin n) U Bool Bool hn hωn hun P π d z.1 H
    (Q.extendedVertices 1) (Q.extendedIndices 1) hH (hpres 1) (by simpa only [Fintype.card_fin] using hpair.1) hpair.2 hrob
    hbalance.1 hbalance.2.1 hbalance.2.2.1 (by simpa only [Nat.cast_add,Nat.cast_ofNat] using hbw)
    (hcuts.2.2.2.1 false) (hcuts.2.2.2.1 true) (hcuts.2.2.2.2 false) (hcuts.2.2.2.2 true)
end Oberwolfach
