module

public import Oberwolfach.OrdinaryInducedRawProbability
public import Oberwolfach.OrdinaryInducedRawPatternExpectation
public import Oberwolfach.OrdinaryInducedRawCandidateDisjoint
public import Oberwolfach.OrdinaryInducedResourceState
public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section
/-! Exact expectation of an induced-wheel omitted-root load under the
original ambient raw product law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
variable (P F : SimpleGraph V) (A : Set V) (u : U) (π : Equiv.Perm V)
    (ρ : Sym2 V → ℝ) (hρ : ∀ e,0≤ρ e) (hρ1 : ∀ e,ρ e≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
local notation "μwheel" => rawWheelLaw ρ hρ hρ1 d hd q hq hQ s hs hS

theorem ordinary_induced_raw_potential_expectation
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (r : ℕ) (hF : permutationConflictGraph π (3*d) ≤ F)
    (w : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r → ℝ)
    (j : Color) (root : Sym2 A ⊕ (A × Unit)) :
    (FiniteLaw.pi μwheel).expectation (fun σ =>
      resourcePatternLoad ordinaryWheelResources w (fun _ _ => true) root
        (ordinaryResourceState ((rawWheelGraph P σ).induce A)
          (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u))) =
      ∑ W, (if root ∈ ordinaryWheelResources W then w W else 0) *
        ∏ a ∈ ordinaryWheelResources W \ {root},
          rawWheelMarginal P ρ s j (ordinaryInducedRawResource A u a) := by
  calc
    _ = ∑ W, (if root ∈ ordinaryWheelResources W then w W else 0) *
        ∏ a ∈ ordinaryWheelResources W \ {root},
          (FiniteLaw.pi μwheel).probability (fun σ =>
            ordinaryResourceState ((rawWheelGraph P σ).induce A)
              (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u) a = true) :=
        ordinary_induced_raw_pattern_expectation P F A u π ρ hρ hρ1 d hd q hq hQ s hs hS r hF w j root
    _ = _ := by
      apply Finset.sum_congr rfl
      intro W _
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      exact ordinary_induced_raw_resource_probability P A u π ρ hρ hρ1 d hd q hq hQ s hs hS hnoshort j a
end Oberwolfach
