module

public import Oberwolfach.MarkedLongVortexInitialGlobalBalance
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
local instance commonBalanceFinDecidable (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem marked_long_common_agreement_initial_global_balance
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
      (startRetentionMinimum (rawStartHubSet π d (fun e=>z.1 (Sum.inr e)) false)) z.2 false false
    let E:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>z.1 (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1
    let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1
    let khead:=fun e:K=>e.val.2;
    (∀v,|occurrenceDegree (Sum.elim tail ktail) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) ∧
    (∀v,|occurrenceDegree (Sum.elim head khead) v-
      (∑u,if H false v u then (1:ℝ) else 0)-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) ∧
    (∀v,|occurrenceDegree khead v-(∑u,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) ∧
    (∀u,|(∑v,if H false v u then (1:ℝ) else 0)-(((r+4):ℕ):ℝ)*(∑v,if H true v u then (1:ℝ) else 0)|≤η*Fintype.card (Fin n)) :=by
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
  have hp:0≤ρ*(1/100)/2:=by positivity
  have hk:0≤ρ*((1/100)/(((r+4):ℕ):ℝ))/2:=by positivity
  have hstatAll:=marked_adaptive_agreement_reference_statistics r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
    (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
    P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight qp sp false false z hEvent hγ hp hk
  have hstat:=hstatAll 0 (by omega)
  have hD: Dlevel 0=(Dnat:ℝ):=marked_vortex_initial_reference_degree Q ρ hρ hsize
  rw [hD] at hstat
  have hneigh:=marked_adaptive_agreement_global_spoke_neighbourhoods r d size a₀ b₀ e₀ aRob bRob eRob f₀ L hNbr
    β βCommon εAbs εRob ζRob εRef δRef γRich (ρ*(1/100)/2)
    (ρ*((1/100)/(((r+4):ℕ):ℝ))/2) (1/100) tstar ζ εBal ζBal εNbr ζNbr Bload εLoad 1 ζLoad ζLocal ζConfig ρ₀ sstar kstar τLevel
    P π fV gV ρi Aset Bset Scale Dlevel Dlevel bdom levelWeight qp sp false false z hEvent
  exact marked_long_assigned_vortex_initial_global_balance hn P π Dnat vsize βQ εQ Q hpres d hNbr r K hh F hF
    θ Dnat ρ εRef δRef (γRich/2) (εNbr*n) (εNbr*Fintype.card U) η z _ hsize hstat
    (by simpa only [Fintype.card_fin] using hneigh.1) hneigh.2 hbudget hmarked hcolumn
end Oberwolfach
