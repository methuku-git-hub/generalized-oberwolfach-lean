module

public import Oberwolfach.OrdinaryInducedRawProbability
public import Oberwolfach.OrdinaryInducedRawCandidateDisjoint
public import Oberwolfach.OrdinaryInducedResourceState
public import Oberwolfach.OrdinaryRawIntervalSampling

@[expose] public section
/-! Exact expectation of an induced-wheel omitted-root load under the
original ambient raw product law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
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

theorem ordinary_induced_raw_pattern_expectation
    (r : ℕ) (hF : permutationConflictGraph π (3*d) ≤ F)
    (w : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r → ℝ)
    (j : Color) (root : Sym2 A ⊕ (A × Unit)) :
    (FiniteLaw.pi μwheel).expectation (fun σ =>
      resourcePatternLoad ordinaryWheelResources w (fun _ _ => true) root
        (ordinaryResourceState ((rawWheelGraph P σ).induce A)
          (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u))) =
      ∑ W, (if root ∈ ordinaryWheelResources W then w W else 0) *
        ∏ a ∈ ordinaryWheelResources W \ {root},
          (FiniteLaw.pi μwheel).probability (fun σ =>
            ordinaryResourceState ((rawWheelGraph P σ).induce A)
              (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u) a = true) := by
  exact resourcePatternLoad_supported_expectation μwheel ordinaryWheelResources w
    (fun _ _ => true) (ordinaryInducedRawCoordinates A u π d)
    (fun σ => ordinaryResourceState ((rawWheelGraph P σ).induce A)
      (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u))
    (ordinary_induced_raw_state_supported P A u π d j) root
    (by
      intro W _ a ha b hb hab
      exact ordinary_induced_raw_candidate_disjoint P F A u π d r hF W a b
        (Finset.mem_sdiff.mp ha).1 (Finset.mem_sdiff.mp hb).1 hab)
end Oberwolfach
