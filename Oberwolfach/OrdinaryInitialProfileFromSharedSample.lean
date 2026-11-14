module

public import Oberwolfach.OrdinaryFixedVortexProfileFromPhysicalInnerScale
public import Oberwolfach.OrdinaryUniformInnerHubEvent

@[expose] public section
/-! The row and adaptive inner-hub tests on one actual sample give the
initial cleanup profile and inner weights for any sufficiently small edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
set_option synthInstance.maxSize 16384
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_profile_from_shared_sample
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U]
    (mWheel d:ℕ) (P G:SimpleGraph V) (Hs:V→U→Prop) (D mv:ℕ)
    (β ε θ α pR pH εR εH L βe βh η b Bweight ηHub capHub:ℝ)
    (Q:Vortex U P D β ε mv) (π:Equiv.Perm V)
    (hπ:∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i)
    (sp:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hn:0<Fintype.card V) (hreg:P.IsRegularOfDegree D) (hρ:0 < initialIndexDensity U D)
    (hβ:0≤β) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hεR:0≤εR) (hεH:0≤εH) (hL:0≤L)
    (hθ:1/2≤θ) (hβα:β≤2*α) (hdegree:(θ+α)*Fintype.card V≤D)
    (hpEq:pR=initialIndexDensity U D*pH) (hsp:∀u,sp u j=pH)
    (hhost:G≤P\permutationConflictGraph π (3*d))
    (hrow:OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D mv β ε Q π hπ pR pH sp j σ)
    (hfamily:OrdinaryUniformInnerHubEvent mWheel P D mv d β ε Q π hπ pR pH βe βh b Bweight ηHub capHub
      (fun _=>θ+α-β/2) (fun k=>εR*(markedVortexInnerVertices Q k).card)
      (fun k=>εH*(markedVortexInnerHubs Q k).card) sp j σ):
    let I:=markedVortexInnerVertices Q 0;let B:=markedVortexInnerHubs Q 0;
    let f:=markedVortexVertexEmbedding Q 0;let g:=markedVortexHubEmbedding Q 0;
    let ρ:=markedVortexPermutation Q π hπ 0;let raw:=ordinaryRawRestrictPair f g σ;
    let Gloc:=G.comap f;let Floc:=(permutationConflictGraph π (3*d)).comap f;
    let Hloc:=fun v u=>Hs (f v) (g u);
    L≤capHub*I.card→
    (∀w:markedVortexVertexType Q 0⊕markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph (P.comap f) raw) (rawWheelSpokes ρ d raw j)).neighborFinset w)
        ((ordinaryPhysicalGraph Gloc Hloc).neighborFinset w)).card:ℝ)≤L)→
    βe*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)+εR*I.card+3*L≤
      pR^2*pH*(2*(θ+α-β/2)-1)*I.card→
    βh*Fintype.card (markedVortexVertexType Q 0⊕markedVortexHubType Q 0)+εH*B.card+2*L≤pH^2*B.card→
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*B.card)+3*L≤η*I.card→
    OrdinaryCleanupParentProfiles (P.comap f) Gloc Floc Hloc ρ d I B pR pH (θ+α-β/2)
      (εR*I.card) (εH*B.card) L βe βh (fun u=>sp (g u)) j raw ∧
    (∀v:I,|((Gloc.induce (I:Set _)).degree v:ℝ)-2*(Finset.univ.filter (fun u:B=>Hloc v.val u.val)).card|≤η*I.card) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel b Bweight ηHub Gloc Floc Hloc I B) :=by
  intro I B f g ρ raw Gloc Floc Hloc hLcap hphys hext hhub hmargin
  have hG:Gloc≤P.comap f:=by intro v w hvw;exact (hhost hvw).1
  have hdis:Disjoint Gloc Floc:=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    exact (hhost hvw.1).2 hvw.2
  have hevent:=hfamily 0 Q.length_pos L hL hLcap
  exact ordinary_fixed_vortex_profile_from_physical_edit_inner_scale mWheel P (permutationConflictGraph π (3*d)) D mv
    β ε θ α pR pH εR εH L βe βh η b Bweight ηHub Q π hπ d sp j σ hn hreg hρ hβ hpR hpR1 hpH hεR hεH hL
    hθ hβα hdegree hpEq hsp hrow 0 Q.length_pos Gloc Hloc hG hdis hphys hext hhub hmargin hevent
end Oberwolfach
