module

public import Oberwolfach.OrdinaryExpandedThreeStepVortexTestsAttach
public import Oberwolfach.OrdinaryVortexLookbackSampleBalance

@[expose] public section
/-! The three-level tests imply edited cross-balance simultaneously for every
admissible edit, with no further random choice. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

def OrdinaryVortexThreeStepEditedBalanceEvent
    (P:SimpleGraph V) (D m:ℕ) (β ε pH εR εH:ℝ)
    (Q:VortexLookback U P D β ε m 2) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i)
    (d:ℕ) (j:Color) (σ:RawWheelOutcome V U Γ Color):Prop:=
  ∀i,i+3≤Q.toVortex.length→
    let T:=ordinaryVortexBufferedVertices Q.toVortex i 3
    let W:=ordinaryVortexBufferedHubs Q.toVortex i 3
    let f:=markedVortexVertexEmbedding Q.toVortex i
    let g:=markedVortexHubEmbedding Q.toVortex i
    let ρ:=markedVortexPermutation Q.toVortex π hπ i
    let raw:=ordinaryRawRestrictPair f g σ
    ∀(L:ℝ),0≤L→∀(G:SimpleGraph (markedVortexVertexType Q.toVortex i))
      (H:markedVortexVertexType Q.toVortex i→markedVortexHubType Q.toVortex i→Prop),
      (∀v,((changed (G.neighborFinset v) ((rawWheelGraph (P.comap f) raw).neighborFinset v)).card:ℝ)≤L)→
      (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes ρ d raw j v))).card:ℝ)≤L)→
      ∀v,|((G.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤
        (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L

theorem ordinary_three_step_balance_event_of_tests
    (P F:SimpleGraph V) (D m:ℕ) (β ε pR pH εR εH:ℝ)
    (Q:VortexLookback U P D β ε m 2) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0 < initialIndexDensity U D)
    (hβ:0≤β) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH) (hpR:pR=initialIndexDensity U D*pH)
    (htests:OrdinaryVortexThreeStepRowIndexEvent 3 d εR εH P F D m β ε Q.toVortex π hπ pR pH s j σ):
    OrdinaryVortexThreeStepEditedBalanceEvent P D m β ε pH εR εH Q π hπ d j σ:=by
  intro i hi T W f g ρ raw L hL G H hrim hspoke
  have tests:=htests i hi
  have hrows:RawOrdinaryRows (P.comap f) ρ d 2 T pR
      (fun u=>s (g u)) j (εR*T.card) raw:=by
    intro S J hS hJ
    exact tests.1 S J (by omega) (by omega)
  exact ordinary_vortex_lookback_sample_balance P F D m 2 β ε pR pH εR εH L Q π hπ d s j σ
    hn hreg hρ hβ hpH hεR hεH hL hpR i G H hrows tests.2 hrim hspoke
end Oberwolfach
