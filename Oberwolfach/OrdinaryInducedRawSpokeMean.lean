module

public import Oberwolfach.OrdinaryInducedRawExpectation
public import Oberwolfach.OrdinaryInducedSpokeProduct

@[expose] public section
/-! Exact omitted-spoke expectation for an induced wheel under the original
ambient raw product law, with fixed wheel coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
variable (P F : SimpleGraph V) (A : Set V) (u : U) (r : ℕ) (hr : 1≤r)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (pR pH : ℝ) (hpR : 0<pR) (hpR1 : pR≤1) (hpH : 0<pH)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j : Color) (hj : s u j=pH)
    (w : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r → ℝ)
local notation "μwheel" => rawWheelLaw (fun _ : Sym2 V => pR) (fun _ => hpR.le) (fun _ => hpR1) d hd q hq hQ s hs hS

include hr hF hnoshort hpH hj

theorem ordinary_induced_raw_spoke_mean (v : A) :
    (FiniteLaw.pi μwheel).expectation (fun σ =>
      resourcePatternLoad ordinaryWheelResources w (fun _ _ => true) (Sum.inr (v,()))
        (ordinaryResourceState ((rawWheelGraph P σ).induce A)
          (fun x (_ : Unit) => rawWheelSpokes π d σ j x.val u))) =
      pR^r*pH^(r-1)*ordinarySpokeLoad w v () := by
  have h1 := ordinary_induced_raw_potential_expectation P F A u π (fun _ => pR) (fun _ => hpR.le)
    (fun _ => hpR1) d hd q hq hQ s hs hS hnoshort r hF w j (Sum.inr (v,()))
  have h2 := ordinary_induced_spoke_marginal_product_sum P F A u r hr s j pR pH hpH hj w v
  convert h1.trans h2 using 1 <;> congr!
end Oberwolfach
