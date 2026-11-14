module

public import Oberwolfach.MarkedLongCommonAgreementGlobalBalance
public import Oberwolfach.MarkedGlobalOccurrenceBalanceToRestricted
public import Oberwolfach.MarkedVortexInitialReferenceDegree
public import Oberwolfach.MarkedAdaptiveAgreementReferenceStatistics
public import Oberwolfach.MarkedAdaptiveAgreementGlobalNeighbourhoods

@[expose] public section
/-! The actual common agreement event supplies all four global marked
near-balance inequalities on the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance commonRestrictedBalanceFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem marked_long_common_agreement_full_restricted_balance
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] [Nonempty (Fin n)]
    (hn:1≤n) (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n))
    (Dnat vsize:ℕ) (βQ εQ:ℝ) (Q:Vortex U P Dnat βQ εQ vsize)
    (hpres:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr:ℕ) (hh:1≤hNbr)
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (θ ρ:ℝ) (hρ:0<ρ) (hsize:ρ*Dnat=2*Fintype.card U)
    (β βCommon εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel η:ℝ)
    (hγ:0≤γRich)
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
    (hbudget:2*(εRef*n)+2*(εNbr*Fintype.card U)≤η*n)
    (hmarked:εRef*n+εNbr*Fintype.card U≤η*n)
    (hcolumn:((((r+4):ℕ):ℝ)+1)*(εNbr*n)≤η*n):
    let H:=retainedRawMarkedSpokes π d (fun e=>z.1 (Sum.inr e)) false
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false;
    MarkedRestrictedBalanceWithSpokes P π d (r+4) Finset.univ Finset.univ (η*n) z.1 H :=by
  intro H
  have hb:=marked_long_common_agreement_initial_global_balance hn P π Dnat vsize βQ εQ Q hpres
    r K d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr hh F hF θ ρ hρ hsize
    β βCommon εAbs εRob ζRob εRef δRef γRich tstar ζ εBal ζBal εNbr ζNbr Bload εLoad ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel η
    hγ levelWeight z hEvent hbudget hmarked hcolumn
  apply marked_global_occurrence_balance_to_restricted P π d (r+4) z.1 H (η*n)
  · simpa only [Fintype.card_fin] using hb.1
  · simpa only [Fintype.card_fin] using hb.2.1
  · simpa only [Fintype.card_fin] using hb.2.2.1
  · simpa only [Fintype.card_fin] using hb.2.2.2
end Oberwolfach
