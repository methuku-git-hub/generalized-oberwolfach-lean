module

public import Oberwolfach.OrdinaryInducedRawSpokeMean
public import Oberwolfach.OrdinarySpokeLocalMeanFromPattern

@[expose] public section
/-! Exact expectation of the induced-domain root-omitted local potential
under the original ambient rim and interval-spoke experiment. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000
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
local notation "μwheel" => rawWheelLaw (fun _ : Sym2 V => pR) (fun _ => hpR.le) (fun _ => hpR1) d hd q hq hQ s hs hS

include hr hF hnoshort hpH hj

theorem ordinary_induced_raw_local_mean (φ : OrdinaryCycle (P.induce A) r → ℝ) (v : A) :
    (FiniteLaw.pi μwheel).expectation (fun σ =>
      ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
        (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u)) φ v) =
      pR^r*pH^(r-1) * ∑ C, if v∈C.val.val.support ∧
        (∀ x∈C.val.val.support,∀ y∈C.val.val.support,¬(F.induce A).Adj x y) then φ C else 0 := by
  have hsp := ordinary_induced_raw_spoke_mean P F A u r hr π d hd hF hnoshort pR pH hpR hpR1 hpH
    q hq hQ s hs hS j hj
    (ordinaryCycleWheelWeight (U:=Unit) (P.induce A) (F.induce A) r φ 1) v
  have hh := ordinary_spoke_local_mean_from_pattern (P.induce A) (F.induce A) r φ
    (FiniteLaw.pi μwheel) (fun σ : RawWheelOutcome V U Γ Color => (rawWheelGraph P σ).induce A)
    (fun σ x (_ : Unit) => rawWheelSpokes π d σ j x.val u) v () (pR^r*pH^(r-1))
    (by convert hsp using 1 <;> congr!)
  convert hh using 1 <;> congr!
end Oberwolfach
