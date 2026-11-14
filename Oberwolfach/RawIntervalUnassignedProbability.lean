module

public import Oberwolfach.RawIntervalFamily
public import Oberwolfach.FiniteCoordinateEvents

@[expose] public section
/-! The unassigned state includes successor endpoints and the unselected
ordinary labels; its mass uses the prescribed interval and ordinary marginals. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem rawIntervalFamily_unassigned_probability
    (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x) (a:V×U):
    (FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)).probability
      (fun σ=>rawIntervalFamilyState π d σ a=none)=1-(∑ g,q a.2 g)-(∑ j,s a.2 j) := by
  let μ:=FiniteLaw.pi (rawIntervalFamilyLaw (V:=V) d hd q hq hQ s hs hS)
  have hh:=finiteLaw_probability_value_partition μ (fun _=>True) (fun σ=>rawIntervalFamilyState π d σ a)
  simp only [finiteLaw_probability_true,true_and,Fintype.sum_option,Fintype.sum_sum_type] at hh
  dsimp only [μ] at hh
  simp_rw [rawIntervalFamily_interval_probability π d hd q hq hQ s hs hS hnoshort,
    rawIntervalFamily_label_probability π d hd q hq hQ s hs hS hnoshort] at hh
  linarith
end Oberwolfach
