module

public import Oberwolfach.OrdinaryInducedRawLocalTargetMean
public import Oberwolfach.OrdinaryMixedHubWeightsFromInducedPotentials

@[expose] public section
/-! All fixed inner hub roots have exactly the target mean under the
original raw law, before any adaptive modifications. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [LinearOrder V] [DecidableEq U]

theorem ordinary_induced_hub_mean_error_zero
    (P F : SimpleGraph V) (H : V → U → Prop) (A : Finset V) (Z : Finset U)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (pR pH D : ℝ) (hpR : 0<pR) (hpR1 : pR≤1) (hpH : 0<pH) (hD : D≠0)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j : Color) (hj : ∀ u, s u j=pH)
    (weight : OrdinaryCycle (P.induce (A : Set V)) 3 → ℝ) :
    let μ := rawWheelLaw (fun _ : Sym2 V => pR) (fun _ => hpR.le) (fun _ => hpR1) d hd q hq hQ s hs hS;
    ∀ u : {u : U // u ∉ Z}, ∀ v ∈ ordinaryInducedLocalDomain A (ordinaryBoundaryHubSet H Z A u),
      |(FiniteLaw.pi μ).expectation (fun τ =>
        ordinaryLocalPotential (P.induce (A : Set V)) ((rawWheelGraph P τ).induce (A : Set V))
          (F.induce (A : Set V))
          (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d τ j x.val u.val))
          (fun C => 2*weight C/(D*pR^3*pH^2)) v) -
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v| ≤ 0 := by
  intro μ u v hv
  have hh := ordinary_induced_raw_local_target_mean P F (A : Set V) u.val π d hd hF hnoshort
    pR pH D hpR hpR1 hpH hD q hq hQ s hs hS j (hj u.val) weight v
  have he : (FiniteLaw.pi μ).expectation (fun τ =>
        ordinaryLocalPotential (P.induce (A : Set V)) ((rawWheelGraph P τ).induce (A : Set V))
          (F.induce (A : Set V))
          (Finset.univ.filter (fun x : {x : V // x ∈ (A : Set V)} => rawWheelSpokes π d τ j x.val u.val))
          (fun C => 2*weight C/(D*pR^3*pH^2)) v) =
        ordinaryLocalTarget (P.induce (A : Set V)) (F.induce (A : Set V)) weight D v := by
    convert hh using 1 <;> congr! <;> (try ext x) <;> simp
  rw [he]
  simp
end Oberwolfach
