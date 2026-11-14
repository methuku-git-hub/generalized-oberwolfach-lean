module

public import Oberwolfach.OrdinaryInducedEditedExpandedPrior
public import Oberwolfach.OrdinaryMixedHubWeightsFromInducedGeneral

@[expose] public section
/-! The adaptive induced-potential event supplies exactly the local hub
potential hypotheses once the mean error and actual edits are controlled. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 4096
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem ordinary_induced_edited_hub_targets_general
    (m:ℕ)
    (P Q F : SimpleGraph V) (H : V → U → Prop) (A : Finset V) (Z : Finset U)
    (π : Equiv.Perm V) (d : ℕ) (j : Color)
    (weight : OrdinaryCycle (P.induce (A : Set V)) (m+1) → ℝ) (D q s : ℝ)
    (μ : ∀ e : RawWheelCoordinate V U, FiniteLaw (RawWheelCoordinateState Γ Color e))
    (σ : RawWheelOutcome V U Γ Color) (B t M L ζ ξ : ℝ)
    (hevent : ordinaryInducedEditedPotentialConcentration P F (A : Set V) π d (m+1) j
      (fun C => 2*weight C/(D*q^(m+1)*s^m)) μ B t M L σ)
    (hQR : ∀ x, (((((rawWheelGraph P σ).induce (A : Set V)) \ (Q.induce (A : Set V))).degree x) : ℝ) ≤ M)
    (hRQ : ∀ x, ((((Q.induce (A : Set V)) \ ((rawWheelGraph P σ).induce (A : Set V))).degree x) : ℝ) ≤ M)
    (hT : ∀ u : {u : U // u ∉ Z},
      (((((Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d σ j x.val u.val)) \
          ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u)) ∪
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u) \
          (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d σ j x.val u.val)))).card : ℝ) ≤ L))
    (hmean : ∀ u : {u : U // u ∉ Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
      |(FiniteLaw.pi μ).expectation (fun τ =>
          ordinaryLocalPotential (P.induce (A : Set V)) ((rawWheelGraph P τ).induce (A : Set V))
            (F.induce (A : Set V))
            (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d τ j x.val u.val))
            (fun C => 2*weight C/(D*q^(m+1)*s^m)) v) -
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ ζ)
    (herr : t + ((m+1:ℕ):ℝ)^2 * B * L / Fintype.card {x : V // x ∈ (A : Set V)} +
      2 * (3 * ((m+1:ℕ):ℝ)^4 * B * M / Fintype.card {x : V // x ∈ (A : Set V)}) + ζ ≤ ξ) :
    ∀ u : {u : U // u ∉ Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
      |ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
        (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u))
        (fun C => 2*weight C/(D*q^(m+1)*s^m)) v -
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ ξ := by
  intro u v hv
  have he := hevent v u.val (Q.induce (A : Set V))
    (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u))
    (by intro x; convert hQR x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet])
    (by intro x; convert hRQ x using 1 <;> simp only [← SimpleGraph.ncard_neighborSet])
    (by convert hT u using 1 <;> congr 3 <;> ext x <;> simp)
  have hm := hmean u v hv
  have hh := abs_sub_le
    (ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u)) (fun C => 2*weight C/(D*q^(m+1)*s^m)) v)
    ((FiniteLaw.pi μ).expectation (fun τ => ordinaryLocalPotential (P.induce (A : Set V))
      ((rawWheelGraph P τ).induce (A : Set V)) (F.induce (A : Set V))
      (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d τ j x.val u.val))
      (fun C => 2*weight C/(D*q^(m+1)*s^m)) v))
    (ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v)
  simp only [Set.fintypeCard_eq_ncard] at he herr
  have he' : |ordinaryLocalPotential (P.induce (A : Set V)) (Q.induce (A : Set V)) (F.induce (A : Set V))
      (ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u)) (fun C => 2*weight C/(D*q^(m+1)*s^m)) v -
      (FiniteLaw.pi μ).expectation (fun τ => ordinaryLocalPotential (P.induce (A : Set V))
        ((rawWheelGraph P τ).induce (A : Set V)) (F.induce (A : Set V))
        (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d τ j x.val u.val))
        (fun C => 2*weight C/(D*q^(m+1)*s^m)) v)| ≤
      t + ((m+1:ℕ):ℝ)^2 * B * L / (A : Set V).ncard +
        2 * (3 * ((m+1:ℕ):ℝ)^4 * B * M / (A : Set V).ncard) := by
    convert he using 1 <;> congr! <;> ext x <;> simp
  exact (hh.trans (add_le_add he' hm)).trans herr
end Oberwolfach
