module

public import Oberwolfach.OrdinaryInducedRawLocalMean

@[expose] public section
/-! The normalization used for hub cycle weights makes the mean of the
sampled induced local potential exactly its fixed fractional target. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
variable (P F : SimpleGraph V) (A : Set V) (u : U)
    (π : Equiv.Perm V) (d : ℕ) (hd : 2≤d)
    (hF : permutationConflictGraph π (3*d)≤F)
    (hnoshort : ∀ x k,0<k → k<2*d+1 → (π^k) x≠x)
    (pR pH D : ℝ) (hpR : 0<pR) (hpR1 : pR≤1) (hpH : 0<pH) (hD : D≠0)
    (q : U → Γ → ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U → Color → ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (j : Color) (hj : s u j=pH)
local notation "μwheel" => rawWheelLaw (fun _ : Sym2 V => pR) (fun _ => hpR.le) (fun _ => hpR1) d hd q hq hQ s hs hS

include hF hnoshort hpH hD hj

theorem ordinary_induced_raw_local_target_mean
    (weight : OrdinaryCycle (P.induce A) 3 → ℝ) (v : A) :
    (FiniteLaw.pi μwheel).expectation (fun σ =>
      ordinaryLocalPotential (P.induce A) ((rawWheelGraph P σ).induce A) (F.induce A)
        (Finset.univ.filter (fun x : A => rawWheelSpokes π d σ j x.val u))
        (fun C => 2*weight C/(D*pR^3*pH^2)) v) =
      ordinaryLocalTarget (P.induce A) (F.induce A) weight D v := by
  rw [ordinary_induced_raw_local_mean P F A u 3 (by omega) π d hd hF hnoshort pR pH hpR hpR1 hpH
    q hq hQ s hs hS j hj]
  unfold ordinaryLocalTarget
  norm_num only [show 3-1=2 by omega]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs
  · field_simp [hD, hpR.ne', hpH.ne']
    <;> ring
  · ring
end Oberwolfach
