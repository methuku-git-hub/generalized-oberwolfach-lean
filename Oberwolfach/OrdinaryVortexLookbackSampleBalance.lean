module

public import Oberwolfach.OrdinaryRawRowsPairRestriction
public import Oberwolfach.OrdinaryVortexLookbackParentBalance
public import Oberwolfach.OrdinarySameSampleBalanceProfiles

@[expose] public section
/-! The two-level-deep sampled tests and original vortex mean yield the
actual deep cross balance after a bounded edit, on the same raw outcome. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_vortex_lookback_sample_balance
    (P F:SimpleGraph V) (D m t:ℕ) (β ε pR pH εR εH L:ℝ)
    (Q:VortexLookback U P D β ε m t) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.toVortex.extendedVertices i↔x∈Q.toVortex.extendedVertices i)
    (d:ℕ) (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D)
    (hρ:0< initialIndexDensity U D) (hβ:0≤β) (hpH:0≤pH)
    (hεR:0≤εR) (hεH:0≤εH) (hL:0≤L) (hpR:pR=initialIndexDensity U D*pH)
    (i:ℕ):
    let T:=ordinaryVortexBufferedVertices Q.toVortex i (t+1);let W:=ordinaryVortexBufferedHubs Q.toVortex i (t+1);
    let f:=markedVortexVertexEmbedding Q.toVortex i;let g:=markedVortexHubEmbedding Q.toVortex i;
    let ρ:=markedVortexPermutation Q.toVortex π hπ i;let raw:=ordinaryRawRestrictPair f g σ;
    ∀(G:SimpleGraph (markedVortexVertexType Q.toVortex i)) (H:markedVortexVertexType Q.toVortex i→markedVortexHubType Q.toVortex i→Prop),
    RawOrdinaryRows (P.comap f) ρ d 2 T pR (fun u=>s (g u)) j (εR*T.card) raw→
    RawOrdinaryDomainIndices (F.comap f) ρ d 3 W pH j (εH*W.card) raw→
    (∀v,((changed (G.neighborFinset v) ((rawWheelGraph (P.comap f) raw).neighborFinset v)).card:ℝ)≤L)→
    (∀v,((changed (Finset.univ.filter (H v)) (Finset.univ.filter (rawWheelSpokes ρ d raw j v))).card:ℝ)≤L)→
    ∀v,|((G.neighborFinset v∩T).card:ℝ)-2*(W.filter (H v)).card|≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L:=by
  intro T W f g ρ raw G H hrows hcols hrim hspoke
  have hparent:∀v,|pR*((P.comap f).neighborFinset v∩T).card-2*pH*W.card|≤
      (initialIndexDensity U D*pH)*β*T.card:=by
    intro v
    have hh:=ordinary_vortex_lookback_parent_balance P D m t β ε pH Q hn hreg hρ hβ hpH i v
    rw [hpR]
    simpa only [Finset.inter_comm] using hh
  have hh:=ordinary_same_sample_balance_profiles (P.comap f) (F.comap f) G H ρ d T W pR pH
    (εR*T.card) (εH*W.card) ((initialIndexDensity U D*pH)*β*T.card) L
    (by positivity) (by positivity) (by positivity) hL (fun u=>s (g u)) j raw
    hrows hcols hparent hrim hspoke
  exact hh.1
end Oberwolfach
