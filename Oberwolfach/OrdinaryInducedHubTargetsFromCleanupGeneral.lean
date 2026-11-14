module

public import Oberwolfach.OrdinaryInducedOriginalHubTargetsGeneral
public import Oberwolfach.OrdinaryInducedRimEditBounds
public import Oberwolfach.OrdinaryInducedSpokeEditBounds

@[expose] public section
/-! The original cleanup profile supplies the adaptive induced-rim and
spoke-edit hypotheses for the sampled hub-potential targets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2500000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem ordinary_induced_hub_targets_from_cleanup_general
    (m:ℕ)
    (P Q F : SimpleGraph V) (H : V → U → Prop) (A : Finset V) (Z : Finset U)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d) (j : Color)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (weight : OrdinaryCycle (P.induce (A : Set V)) (m+1) → ℝ) (D pR pH : ℝ)
    (hpR : 0<pR) (hpR1 : pR≤1) (hpH : 0<pH) (hD : D≠0)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (σ : RawWheelOutcome V U Γ Color) (B t Ledit ξ density tR tH βe βh : ℝ)
    (profile : OrdinaryCleanupParentProfiles P Q F H π d A Z pR pH density tR tH Ledit βe βh s j σ) :
    let μ := rawWheelLaw (fun _ : Sym2 V => pR) (fun _ => hpR.le) (fun _ => hpR1) d hd q hq hQ s hs hS;
    ordinaryInducedEditedPotentialConcentration P F (A : Set V) π d (m+1) j
      (fun C => 2*weight C/(D*pR^(m+1)*pH^m)) μ B t Ledit Ledit σ →
    t + ((m+1:ℕ):ℝ)^2 * B * Ledit / Fintype.card {x : V // x ∈ (A : Set V)} +
      2 * (3 * ((m+1:ℕ):ℝ)^4 * B * Ledit / Fintype.card {x : V // x ∈ (A : Set V)}) ≤ ξ →
    ∀ u : {u : U // u ∉ Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
      |ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u))
        (fun C => 2*weight C/(D*pR^(m+1)*pH^m)) v -
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ ξ := by
  intro μ hevent herr
  have hedit := ordinary_induced_rim_edit_bounds (rawWheelGraph P σ) Q (A : Set V) Ledit profile.rim_edit
  have hspoke (u : {u : U // u ∉ Z}) :=
    (ordinary_induced_spoke_change_le_ambient (rawWheelSpokes π d σ j) H A Z u).trans
      (profile.spoke_column_edit u.val)
  apply ordinary_induced_original_hub_targets_general m P Q F H A Z π d hd j hF hnoshort weight D pR pH
    hpR hpR1 hpH hD q hq hQ s hs hS profile.spoke_probability σ B t Ledit Ledit ξ hevent
  · intro x
    convert hedit.1 x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]
  · intro x
    convert hedit.2 x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet]
  · intro u
    convert hspoke u using 1 <;> simp only [changed] <;> congr! <;> (try ext x) <;> simp
  · exact herr
end Oberwolfach
