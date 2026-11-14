module

public import Oberwolfach.OrdinaryInitialActualHostSampleBundle
public import Oberwolfach.OrdinaryFixedVortexProfileFromPhysicalInnerScale
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

theorem ordinary_initial_actual_host_physical_bundle
    {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [LinearOrder U]
    (mWheel : ℕ) (P G : SimpleGraph V) (Hs : V → U → Prop) (D m : ℕ)
    (β ε θ α pR pH εR εH L βe βh η bHub BHub ηHub capHub : ℝ)
    (Q : Vortex U P D β ε m) (π : Equiv.Perm V)
    (hπ : ∀ i x, π x ∈ Q.extendedVertices i ↔ x ∈ Q.extendedVertices i)
    (d : ℕ) (s : U → Color → ℝ) (j : Color) (σ : RawWheelOutcome V U Γ Color)
    (hn : 0 < Fintype.card V) (hreg : P.IsRegularOfDegree D)
    (hρ : 0 < initialIndexDensity U D) (hβ : 0 ≤ β) (hpR0 : 0 ≤ pR) (hpR1 : pR ≤ 1) (hpH : 0 ≤ pH)
    (hεR : 0 ≤ εR) (hεH : 0 ≤ εH) (hL : 0 ≤ L)
    (hθ : 1/2 ≤ θ) (hβα : β ≤ 2*α) (hdegree : (θ+α)*Fintype.card V ≤ D) (hpR : pR=initialIndexDensity U D*pH) (hs : ∀u, s u j=pH)
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
    (∀ z : markedVortexVertexType Q 0 ⊕ markedVortexHubType Q 0,
      ((changed ((ordinaryPhysicalGraph (rawWheelGraph Ploc raw) (rawWheelSpokes ρ d raw j)).neighborFinset z)
        ((ordinaryPhysicalGraph Gloc Hloc).neighborFinset z)).card : ℝ) ≤ L) →
    βe*Fintype.card (markedVortexVertexType Q 0 ⊕ markedVortexHubType Q 0)+εR*I.card+3*L ≤
      pR^2*pH*(2*(θ+α-β/2)-1)*I.card →
    βh*Fintype.card (markedVortexVertexType Q 0 ⊕ markedVortexHubType Q 0)+εH*J.card+2*L ≤ pH^2*J.card →
    (initialIndexDensity U D*pH)*β*I.card+εR*I.card+2*(εH*J.card)+3*L ≤ η*I.card →
    OrdinaryCleanupParentProfiles Ploc Gloc Floc Hloc ρ d I J pR pH (θ+α-β/2)
      (εR*I.card) (εH*J.card) L βe βh (fun u => s (g u)) j raw ∧
    Gloc ≤ Ploc \ Floc ∧
    (∀ v, Gloc.degree v=2*(Finset.univ.filter (Hloc v)).card) ∧
    (∀ u, (mWheel+1) ∣ (Finset.univ.filter (fun v => Hloc v u)).card) ∧
    (∀ v : I, |((Gloc.induce (I : Set _)).degree v : ℝ)-
      2*(Finset.univ.filter (fun u : J => Hloc v.val u.val)).card| ≤ η*I.card) ∧
    (∀ v ∉ I, |((Gloc.neighborFinset v ∩ I).card : ℝ)-2*(J.filter (Hloc v)).card| ≤ η*I.card) ∧
    (∀ v ∉ T, |((Gloc.neighborFinset v ∩ T).card : ℝ)-2*(W.filter (Hloc v)).card| ≤
      (initialIndexDensity U D*pH)*β*T.card+εR*T.card+2*(εH*W.card)+3*L) ∧
    Nonempty (OrdinaryMixedHubWeightsInnerScale mWheel bHub BHub ηHub Gloc Floc Hloc I J) := by
  intro f g I J T W ρ raw Ploc Floc Gloc Hloc hcap hphysical hext hhub hmargin
  have hlocal : Gloc ≤ Ploc \ Floc := by
    intro v w h
    exact hG h
  have hdis : Disjoint Gloc Floc := by
    apply disjoint_iff_inf_le.mpr
    intro v w h
    exact (hlocal h.1).2 h.2
  have hevent := hfamily 0 Q.length_pos L hL hcap
  have hprofile := (ordinary_fixed_vortex_profile_from_physical_edit_inner_scale mWheel P (permutationConflictGraph π (3*d))
    D m β ε θ α pR pH εR εH L βe βh η bHub BHub ηHub Q π hπ d s j σ
    hn hreg hρ hβ hpR0 hpR1 hpH hεR hεH hL hθ hβα hdegree hpR hs hgood 0 Q.length_pos Gloc Hloc
    (by intro v w h;exact (hlocal h).1) hdis hphysical hext hhub hmargin
    (by convert hevent using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _)).1
  have hrest := ordinary_initial_actual_host_sample_bundle mWheel P G Hs D m β ε θ α pR pH εR εH L βe βh η bHub BHub ηHub capHub
    Q π hπ d s j σ hn hreg hρ hβ hpH hεR hεH hL hdegree hpR hG hbal hdiv hgood hgood2 hfamily
    hcap (by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _) hphysical hmargin
  exact ⟨(by convert hprofile using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _), hrest⟩
end Oberwolfach
