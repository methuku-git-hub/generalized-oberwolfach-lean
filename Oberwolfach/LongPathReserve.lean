module

public import Oberwolfach.LongIntervalMixing
public import Oberwolfach.TransitionPathEdgeMarginals
public import Oberwolfach.FinitePathMarginals

@[expose] public section

/-! The reserve on actual long paths has the prescribed endpoint matrix and
uses at most eleven twenty-sevenths of every original capacity. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_reserved_path_edge_bound {X : Type*} [Fintype X]
    (R : ℕ → X → X → ℝ) (π : ℕ → X → ℝ)
    (hR : ∀ i, IsTransition (R i)) (hπpos : ∀ i x, 0 < π i x)
    (hπsum : ∀ i, ∑ x, π i x=1)
    (hπ : ∀ i, transitionApply (π i) (R i)=π (i+1))
    (J : Finset ℕ) (hJ : J.card ≤ 1) (κ B M : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hB : 1 ≤ B)
    (a L t : ℕ)
    (ht : 1+3*⌈Real.log (10*(B+1)) / (-Real.log (1-κ))⌉₊ ≤ t)
    (hL : 4*t+1 ≤ L)
    (hupper : ∀ i, a ≤ i → i < a+L → i ∉ J → ∀ x y, R i x y ≤ B*π (i+1) y)
    (hminor : ∀ i, a ≤ i → i+3 ≤ a+L → i ∉ J → i+1 ∉ J → i+2 ∉ J →
      ∀ x y, κ*π (i+3) y ≤ transitionWalk R i 3 x y)
    (Q : X → X → ℝ)
    (hQ : Q ∈ transportMatrices (fun x => M*π a x/3) (fun z => M*π (a+L) z/3))
    (e : Fin L) (v w : X) :
    pathEdgeLoad (reservedPathWeight R a L Q) e v w ≤
      (11/27)*(M*π (a+e.val) v*R (a+e.val) v w) := by
  have hπ0 := fun i x => (hπpos i x).le
  have hwhole := long_interval_mixing R π hR hπ0 hπsum hπ J hJ κ B hκ hκ1 hB
    a L t hupper hminor ht (by omega)
  have hT (x z : X) : (9/10)*π (a+L) z ≤ transitionWalk R a L x z := by
    have hh := (abs_le.mp (hwhole x z)).1
    linarith
  have hsub (s l : ℕ) (has : a ≤ s) (hsl : s+l ≤ a+L)
      (hclean : HasCleanBlock J s l t) :
      ∀ x, RelativeError (transitionWalk R s l x) (π (s+l)) (1/10) := by
    obtain ⟨b,hsb,hbt,hgood⟩ := hclean
    exact transitionWalk_mixing_from_subinterval R π hR hπ s l b t hsb hbt (1/10)
      (clean_block_mixing R π hR hπ0 hπsum hπ J κ B hκ hκ1 hB b t
        (fun i hi hiend => hupper i (by omega) (by omega))
        (fun i hi hiend => hminor i (by omega) (by omega)) ht hgood)
  change (∑ p : Fin (L+1) → X, if p e.castSucc=v ∧ p e.succ=w then reservedPathWeight R a L Q p else 0) ≤ _
  rw [reservedPathWeight_edge_marginal]
  obtain hp | hs := edge_has_clean_prefix_or_suffix J hJ a L t (a+e.val) hL (by omega) (by omega)
  · have hp' : HasCleanBlock J a e.val t := by simpa only [Nat.add_sub_cancel_left] using hp
    have hpre := hsub a e.val le_rfl (by omega) hp'
    apply reservedEdgeLoad_prefix_bound Q _ _ _ _ (π (a+e.val)) (π (a+L)) M hQ.1
      (hR (a+e.val)).1 (transitionWalk_isTransition R hR _ _)
      (hπ0 _) (hπpos _) hQ.2.2 hT
    intro x y
    have hh := (abs_le.mp (hpre x y)).2
    linarith
  · have hs' : HasCleanBlock J (a+e.val+1) (L-e.val-1) t := by
      convert hs using 1 <;> omega
    have hsuf := hsub (a+e.val+1) (L-e.val-1) (by omega) (by omega) hs'
    have hend : a+e.val+1+(L-e.val-1)=a+L := by omega
    rw [hend] at hsuf
    apply reservedEdgeLoad_suffix_bound Q _ _ _ _ (fun x => M*π a x)
      (fun y => M*π (a+e.val) y) (π (a+L)) hQ.1
      (transitionWalk_isTransition R hR _ _).1 (hR (a+e.val)).1 hQ.2.1
      ?_ (hπpos _) hT ?_
    · intro y
      simp only [mul_assoc, ← Finset.mul_sum]
      congr 1
      exact congrFun (transitionWalk_stationary R π hπ a e.val) y
    · intro y z
      have hh := (abs_le.mp (hsuf y z)).2
      linarith

end Oberwolfach
