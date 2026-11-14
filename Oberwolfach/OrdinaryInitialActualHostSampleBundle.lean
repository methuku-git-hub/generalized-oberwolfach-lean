module

public import Oberwolfach.OrdinaryInitialHostSupport
public import Oberwolfach.OrdinaryFixedVortexCleanupBalance
public import Oberwolfach.OrdinaryFixedVortexCleanupBothBalance
public import Oberwolfach.OrdinaryVortexInitialZeroTwoStepDeepBalance
public import Oberwolfach.OrdinaryUniformInnerHubEvent

@[expose] public section
/-! On the actual initial remainder, the common sampled events and one
physical edit yield both balances, deeper balance and the adaptive weights. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_initial_actual_host_sample_bundle
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder U]
    (mWheel : ℕ) (P G : SimpleGraph V) (Hs : V → U → Prop) (D m : ℕ)
    (β ε θ α pR pH εR εH L βe βh η bHub BHub ηHub capHub : ℝ)
    (Q : Vortex U P D β ε m) (π : Equiv.Perm V)
    (hπ : ∀ i x, π x ∈ Q.extendedVertices i ↔ x ∈ Q.extendedVertices i)
    (d : ℕ) (s : U → Color → ℝ) (j : Color) (σ : RawWheelOutcome V U Γ Color)
    (hn : 0 < Fintype.card V) (hreg : P.IsRegularOfDegree D)
    (hρ : 0 < initialIndexDensity U D) (hβ : 0 ≤ β) (hpH : 0 ≤ pH)
    (hεR : 0 ≤ εR) (hεH : 0 ≤ εH) (hL : 0 ≤ L)
    (hdegree : (θ+α)*Fintype.card V ≤ D) (hpR : pR=initialIndexDensity U D*pH)
    (hG : G ≤ P \ permutationConflictGraph π (3*d))
    (hbal : ∀ v, G.degree v=2*(Finset.univ.filter (Hs v)).card)
    (hdiv : ∀ u, (mWheel+1) ∣ (Finset.univ.filter (fun v => Hs v u)).card)
    (hgood : OrdinaryFixedVortexRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (hgood2 : OrdinaryVortexTwoStepRowIndexEvent 3 d εR εH P (permutationConflictGraph π (3*d)) D m β ε Q π hπ pR pH s j σ)
    (hfamily : OrdinaryUniformInnerHubEvent mWheel P D m d β ε Q π hπ pR pH βe βh bHub BHub ηHub capHub
      (fun _ => θ+α-β/2) (fun i => εR*(markedVortexInnerVertices Q i).card)
      (fun i => εH*(markedVortexInnerHubs Q i).card) s j σ) :
    let f := markedVortexVertexEmbedding Q 0; let g := markedVortexHubEmbedding Q 0
    let I := markedVortexInnerVertices Q 0; let J := markedVortexInnerHubs Q 0
    let T := ordinaryVortexBufferedVertices Q 0 2; let W := ordinaryVortexBufferedHubs Q 0 2
    let ρ := markedVortexPermutation Q π hπ 0; let raw := ordinaryRawRestrictPair f g σ
    let Ploc := P.comap f; let Floc := (permutationConflictGraph π (3*d)).comap f
    let Gloc := G.comap f; let Hloc := fun v u => Hs (f v) (g u);
    L ≤ capHub*I.card →
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρ d I J pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) L βe βh (fun u => s (g u)) j raw →
    (∀ z : markedVortexVertexType Q 0 ⊕ markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph Ploc raw) (rawWheelSpokes ρ d raw j)).neighborFinset z)
        ((ordinaryPhysicalGraph Gloc Hloc).neighborFinset z)).card : ℝ) ≤ L) →
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L ≤ η*I.card →
    Gloc ≤ Ploc \ Floc ∧
    (∀ v, Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀ u, (mWheel+1) ∣ (Finset.univ.filter (fun v => Hloc v u)).card) ∧
    (∀ v : I, |((Gloc.induce (I : Set _)).degree v : ℝ)-
      2*(Finset.univ.filter (fun u : J => Hloc v.val u.val)).card| ≤ η*I.card) ∧
    (∀ v ∉ I, |((Gloc.neighborFinset v ∩ I).card : ℝ)-2*(J.filter (Hloc v)).card| ≤ η*I.card) ∧
    (∀ v ∉ T, |((Gloc.neighborFinset v ∩ T).card : ℝ)-2*(W.filter (Hloc v)).card| ≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub BHub ηHub Gloc Floc Hloc I J) := by
  intro f g I J T W ρ raw Ploc Floc Gloc Hloc hcap hprofile hphysical hmargin
  have hlocal : Gloc ≤ Ploc \ Floc := by
    intro v w h
    exact hG h
  have hsupport := ordinary_initial_host_support P G Hs D m β ε Q
  have hexact := ordinary_vortex_supported_local_exact_balance P G Hs D m β ε Q (mWheel+1) 0 hsupport hbal hdiv
  have hnear := ordinary_fixed_vortex_cleanup_balance P (permutationConflictGraph π (3*d)) D m β ε θ α pR pH εR εH L βe βh η
    Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpR hgood 0 Q.length_pos Gloc Hloc hprofile hmargin
  have hboth := ordinary_fixed_vortex_cleanup_both_balance P (permutationConflictGraph π (3*d)) D m β ε θ α pR pH εR εH L βe βh η
    Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpR hgood 0 Q.length_pos Gloc Hloc hprofile hmargin
  have hdeep := ordinary_vortex_initial_zero_two_step_deep_balance P (permutationConflictGraph π (3*d)) D m β ε pR pH εR εH L
    Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hpR hgood2 Gloc Hloc hphysical
  have hevent := hfamily 0 Q.length_pos L hL hcap
  have hweights := hevent Gloc Hloc (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) (by intro v w h; exact (hlocal h).1)
  refine ⟨hlocal, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; convert hexact.1 v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro u; convert hexact.2 u using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v; convert hnear v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv; convert hboth.2 v hv using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · intro v hv; convert hdeep v using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  · convert hweights using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
