module

public import Oberwolfach.LongAssignedSamplingRecipe
public import Oberwolfach.MarkedAdaptiveAgreementReferenceFields
public import Oberwolfach.MarkedAdaptiveAgreementGlobalSpokeError
public import Oberwolfach.MarkedVortexInitialExtendedEquivs
public import Oberwolfach.MarkedRetainedFourCutsFromRelabel

@[expose] public section
/-! The common agreement event supplies the four global correction cuts
on the same original retained sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonCutsFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem marked_long_common_agreement_initial_four_cuts
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (hn:1≤n) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρ:0<ρ) (hDnat:0<Dnat) (hsize:ρ*Dnat=2*Fintype.card U)
    (β βCommon εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel η:ℝ)
    (hγ:0<γRich)
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
    (hkstar:0<kstar) (htstar:0<tstar) (htstar1:tstar≤1) (hεNbr:0≤εNbr)
    (hpmin:kstar≤ρ*(1/100)/2) (hkmin:kstar≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (hbudget:εNbr/(2*((hNbr:ℝ)+1))≤14*(min ((γRich/2)*kstar) tstar/128)):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let δ:=min (min (γRich/2) kstar) tstar/256
    let h:=min ((γRich/2)*kstar) tstar/128;
    0<δ ∧ δ<1/4 ∧ 0<h ∧
    (∀mark,BipartiteLargeCut
      (occurrenceMultiplicity (fun e:MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) mark=>e.val.1)
        (fun e=>e.val.2)) δ (2*h)) ∧
    (∀mark,BipartiteLargeCut (relationMultiplicity (H mark)) δ (2*h)):=by
  let fV:=markedVortexVertexEmbedding Q
  let gV:=markedVortexHubEmbedding Q
  let ρi:=markedVortexPermutation Q π hpres
  let Aset:=markedVortexInnerVertices Q
  let Bset:=markedVortexInnerHubs Q
  let Scale:=fun i=>Fintype.card (markedVortexVertexType Q i)
  let Dlevel:=fun i=>2*(Fintype.card (markedVortexHubType Q i):ℝ)/ρ
  let bdom:=fun i=>Function.Embedding.refl (markedVortexHubType Q i)
  let qp:=longAssignedIntervalProbability F hF K (r+4) θ
  let sp:=longAssignedSpokeProbability F hF K (r+4) θ
  let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
  let δ:=min (min (γRich/2) kstar) tstar/256
  let h:=min ((γRich/2)*kstar) tstar/128
  have hp:0≤ρ*(1/100)/2:=by positivity
  have hk:0≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2:=by positivity
  have hfields:=marked_adaptive_agreement_reference_fields r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
    (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
    P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight qp sp false false z hEvent hγ.le hp hk
  have hlocalCut:=(hfields 0 (by omega)).2
  have herr:=marked_adaptive_agreement_global_spoke_error r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
    (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
    P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight qp sp false false z hEvent
  let f:=markedVortexInitialExtendedVertexEquiv Q
  let uEq:=markedVortexInitialExtendedHubEquiv Q
  letI:Nonempty (markedVortexVertexType Q 0):=⟨f.symm (Classical.choice inferInstance)⟩
  let πW:=markedVortexPermutation Q π hpres 0
  have hf:∀w,f w=markedVortexVertexEmbedding Q 0 w:=by intro w;rfl
  have hc:∀w,f (πW w)=π (f w):=marked_vortex_initial_extended_equiv_commutes Q π hpres
  have hcut':MarkedReferenceCutFamilies (P.comap (markedVortexVertexEmbedding Q 0)) πW d false false
      (γRich/2) (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) tstar
      (markedRetainedPairRestriction f uEq π πW hc d false z).1:=by
    convert hlocalCut using 1
    rfl
  have hUpos:0<Fintype.card U:=by
    have hD:(0:ℝ)<Dnat:=by exact_mod_cast hDnat
    have hp':0<(Fintype.card U:ℝ):=by nlinarith [mul_pos hρ hD,hsize]
    exact_mod_cast hp'
  have hZ:0<Fintype.card (markedVortexHubType Q 0):=by
    rw [Fintype.card_congr uEq];exact hUpos
  have hζold:0≤εNbr/(2*((hNbr:ℝ)+1)):=by positivity
  have hcuts:=marked_retained_four_cuts_from_reference_relabel (markedVortexVertexEmbedding Q 0) f hf uEq π πW hc P d false false z
    (γRich/2) kstar tstar (ρ*(1/100)/2) (ρ*((1/100)/(((r+4):ℕ):ℝ))/2)
    (by positivity) hkstar htstar hpmin hkmin hZ hcut' H (εNbr/(2*((hNbr:ℝ)+1))) hζold herr.1 herr.2 hbudget
  have hδ:0<δ:=by dsimp [δ];positivity
  have hδsmall:δ<1/4:=by
    have hh:=min_le_right (min (γRich/2) kstar) tstar
    dsimp [δ]
    linarith
  have hh:0<h:=by dsimp [h];positivity
  exact ⟨hδ,hδsmall,hh,hcuts⟩
end Oberwolfach
