module

public import Oberwolfach.MarkedRetainedPairRestriction
public import Oberwolfach.VortexInitialDomainInverse

@[expose] public section
/-! The initial vortex domains carry exactly the original two-stage marked
law under the canonical relabellings. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [Nonempty V] [LinearOrder V] [DecidableEq U]

variable (G : SimpleGraph V) (D m : ℕ) (β ε : ℝ) (Q : Vortex U G D β ε m)
local instance vortexLawVertexDecEq : DecidableEq V := fun a b => Classical.propDecidable (a = b)
local instance vortexLawLocalVertexDecEq : DecidableEq (Q.vertices 0) := fun a b => Classical.propDecidable (a = b)
local instance vortexLawLocalHubDecEq : DecidableEq (Q.indices 0) := fun a b => Classical.propDecidable (a = b)
local instance vortexLawLocalNonempty : Nonempty (Q.vertices 0) :=
  ⟨vortexInitialVertexOrderIso G D m β ε Q (Classical.choice inferInstance)⟩

theorem marked_vortex_initial_retention_law
    (π : Equiv.Perm V) (d : ℕ) (hd : 2 ≤ d) (a : Γ)
    (p k : ℝ) (hp : 0 ≤ p) (hk : 0 ≤ k) (hphys : 2*p+2*k ≤ 1)
    (q : U → Γ → ℝ) (hq : ∀ u c, 0 ≤ q u c) (hQ : ∀ u, ∑ c, q u c ≤ 1/8)
    (s : U → Color → ℝ) (hs : ∀ u c, 0 ≤ s u c)
    (hS : ∀ u, ∑ c, s u c ≤ intervalUncoveredProbability d (∑ c, q u c)) :
    let f := vortexInitialVertexEquiv G D m β ε Q
    let g := (vortexInitialHubEquiv G D m β ε Q).symm
    let ρ := vortexInitialPermutation G D m β ε Q π
    let hc : ∀ x, f (ρ x) = π (f x) := vortex_initial_permutation_commutes G D m β ε Q π
    ∀ E : RawMarkedRetainedOutcome (U:=Q.indices 0) (Color:=Color) ρ d a → Prop,
    (rawMarkedRetentionLaw π d hd a p k hp hk hphys q hq hQ s hs hS).probability
      (fun z => E (markedRetainedPairRestriction f g π ρ hc d a z)) =
    (rawMarkedRetentionLaw ρ d hd a p k hp hk hphys (fun z => q (g z))
      (fun z => hq (g z)) (fun z => hQ (g z)) (fun z => s (g z))
      (fun z => hs (g z)) (fun z => hS (g z))).probability E := by
  dsimp only
  intro E
  exact marked_retained_pair_restriction_probability (vortexInitialVertexEquiv G D m β ε Q)
    (vortexInitialHubEquiv G D m β ε Q).symm π (vortexInitialPermutation G D m β ε Q π)
    (vortex_initial_permutation_commutes G D m β ε Q π) d hd a p k hp hk hphys q hq hQ s hs hS E
end Oberwolfach
