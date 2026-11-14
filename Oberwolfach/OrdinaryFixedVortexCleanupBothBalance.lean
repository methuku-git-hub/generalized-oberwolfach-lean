module

public import Oberwolfach.OrdinaryFixedVortexCleanupInputs
public import Oberwolfach.OrdinaryCleanupParentProfiles
public import Oberwolfach.OrdinarySameSampleBalanceProfiles

@[expose] public section
/-! The fixed-vortex row and index tests and the edited parent profile give
both balance inequalities required by the root reference on one sample. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_fixed_vortex_cleanup_both_balance
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
    (∀v,|((spanningRestriction G I).degree v:ℝ)-
      2*(Finset.univ.filter (fun u=>H v u∧v∈I∧u∈J)).card|≤η*I.card) ∧
    (∀v∉I,|((G.neighborFinset v∩I).card:ℝ)-2*(J.filter (H v)).card|≤η*I.card):=by
  intro V₁ U₁ I J f g ρ raw G H profile hmargin
  have hin:=ordinary_fixed_vortex_cleanup_inputs P F D m β ε θ α pR pH εR εH Q π hπ d s j σ
    hn hreg hρ hβ hpH hdegree hgood i hi
  have hparent:∀v:V₁,|pR*((P.comap f).neighborFinset v∩I).card-2*pH*J.card|≤
      (initialIndexDensity U D*pH)*β*I.card:=by
    intro v
    have hh:=hin.2.1 v
    rw [hpR]
    simpa only [Finset.inter_comm] using hh
  have hrim:∀v,((changed (G.neighborFinset v) ((rawWheelGraph (P.comap f) raw).neighborFinset v)).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.union_comm] using profile.rim_edit v
  have hspoke:∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes ρ d raw j v))).card:ℝ)≤L:=by
    intro v
    simpa [changed,Finset.union_comm] using profile.spoke_row_edit v
  have hh:=ordinary_same_sample_balance_profiles (P.comap f) (F.comap f) G H ρ d I J pR pH
    (εR*I.card) (εH*J.card) ((initialIndexDensity U D*pH)*β*I.card) L
    (by positivity) (by positivity) (by positivity) hL (fun u=>s (g u)) j raw
    profile.rows profile.columns hparent hrim hspoke
  exact ⟨fun v=>(hh.2 v).trans hmargin,fun v _=>(hh.1 v).trans hmargin⟩
end Oberwolfach
