module

public import Oberwolfach.OrdinaryFixedVortexCleanupInputs
public import Oberwolfach.OrdinaryInducedCorrectionBalanceFromSample

@[expose] public section
/-! On every fixed vortex level, the common sample and its original parent
mean give the near-balance input for the actual induced correction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_cleanup_balance
    (P F:SimpleGraph V) (D m:ℕ) (β ε θ α pR pH εR εH L βe βh η:ℝ)
    (Q:Vortex U P D β ε m) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpH:0≤pH)
    (hεR:0≤εR) (hεH:0≤εH) (hL:0≤L)
    (hdegree:(θ+α)*Fintype.card V≤D) (hpR:pR=initialIndexDensity U D*pH)
    (hgood:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P F D m β ε Q π hπ pR pH s j σ)
    (i:ℕ) (hi:i<Q.length):
    let V₁:=markedVortexVertexType Q i;let U₁:=markedVortexHubType Q i;
    let I:=markedVortexInnerVertices Q i;let J:=markedVortexInnerHubs Q i;
    let f:=markedVortexVertexEmbedding Q i;let g:=markedVortexHubEmbedding Q i;
    let ρ:=markedVortexPermutation Q π hπ i;
    let raw:=ordinaryRawRestrictPair f g σ;
    ∀(G:SimpleGraph V₁) (H:V₁→U₁→Prop),
    OrdinaryCleanupParentProfiles (P.comap f) G (F.comap f) H ρ d I J pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) L βe βh (fun u=>s (g u)) j raw→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L≤η*I.card→
    ∀v:I,|(((G.induce (I:Set V₁)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:J=>H v.val u.val)).card|≤η*I.card:=by
  intro V₁ U₁ I J f g ρ raw G H hprofile hmargin
  have hin:=ordinary_fixed_vortex_cleanup_inputs P F D m β ε θ α pR pH εR εH Q π hπ d s j σ
    hn hreg hρ hβ hpH hdegree hgood i hi
  have hparent:∀v:V₁,|pR*((P.comap f).neighborFinset v∩I).card-2*pH*J.card|≤
      (initialIndexDensity U D*pH)*β*I.card:=by
    intro v
    have hh:=hin.2.1 v
    rw [hpR]
    simpa only [Finset.inter_comm] using hh
  have htR:0≤εR*(I.card:ℝ):=by positivity
  have htH:0≤εH*(J.card:ℝ):=by positivity
  have he:0≤(initialIndexDensity U D*pH)*β*(I.card:ℝ):=by positivity
  exact ordinary_induced_correction_balance_from_sample (P.comap f) G (F.comap f) H ρ d I J
    pR pH (θ+α-β/2) (εR*I.card) (εH*J.card) ((initialIndexDensity U D*pH)*β*I.card)
    L βe βh η htR htH he hL (fun u=>s (g u)) j raw hprofile hparent hmargin
end Oberwolfach
