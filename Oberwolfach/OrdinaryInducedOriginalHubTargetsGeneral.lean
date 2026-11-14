module

public import Oberwolfach.OrdinaryInducedHubMeanErrorZeroGeneral
public import Oberwolfach.OrdinaryInducedEditedHubTargetsGeneral

@[expose] public section
/-! The original raw law supplies the mean hypothesis in the adaptive
hub-target bridge. The edit and numeric bounds remain explicit. -/
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

theorem ordinary_induced_original_hub_targets_general
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
    (hj : ∀ u, s u j=pH)
    (σ : RawWheelOutcome V U Γ Color) (B t M L ξ : ℝ) :
    let μ := rawWheelLaw (fun _ : Sym2 V => pR) (fun _ => hpR.le) (fun _ => hpR1) d hd q hq hQ s hs hS;
    ordinaryInducedEditedPotentialConcentration P F (A : Set V) π d (m+1) j
      (fun C => 2*weight C/(D*pR^(m+1)*pH^m)) μ B t M L σ →
    (∀ x, (((((rawWheelGraph P σ).induce (A : Set V)) \ (Q.induce (A : Set V))).degree x) : ℝ) ≤ M) →
    (∀ x, ((((Q.induce (A : Set V)) \ ((rawWheelGraph P σ).induce (A : Set V))).degree x) : ℝ) ≤ M) →
    (∀ u : {u : U // u ∉ Z},
      (((((Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d σ j x.val u.val)) \
          ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u)) ∪
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u) \
          (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d σ j x.val u.val)))).card : ℝ) ≤ L)) →
    t + ((m+1:ℕ):ℝ)^2 * B * L / Fintype.card {x : V // x ∈ (A : Set V)} +
      2 * (3 * ((m+1:ℕ):ℝ)^4 * B * M / Fintype.card {x : V // x ∈ (A : Set V)}) ≤ ξ →
    ∀ u : {u : U // u ∉ Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
      |ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u))
        (fun C => 2*weight C/(D*pR^(m+1)*pH^m)) v -
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ ξ := by
  intro μ hevent hQR hRQ hT herr
  have hm := ordinary_induced_hub_mean_error_zero_general m P F H A Z π d hd hF hnoshort pR pH D
    hpR hpR1 hpH hD q hq hQ s hs hS j hj weight
  have hh := ordinary_induced_edited_hub_targets_general m P Q F H A Z π d j weight D pR pH μ σ B t M L 0 ξ
    hevent hQR hRQ hT (by convert hm using 1 <;> congr!) (by linarith)
  exact hh
end Oberwolfach
