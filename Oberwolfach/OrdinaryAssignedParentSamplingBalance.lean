module

public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The ordinary assigned sampling recipe supplies the fixed reserved-spoke
    marginal and the original parent mean balance without assuming regularity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_parent_sampling_balance
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2) (i₀:Fin K)
    (rsv θ c ρ D p k p₂ k₂ u:ℝ)
    (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1)
    (hsize:ρ*D=2*(Fintype.card U:ℝ)) (hpEq:2*p=ρ*rsv) :
    0≤2*p ∧ 2*p≤1 ∧ (2*p)*D=2*(Fintype.card U:ℝ)*rsv ∧
      ∀w,ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c w false=rsv := by
  refine ⟨by positivity,by linarith,?_,?_⟩
  · calc
      (2*p)*D=(ρ*rsv)*D:=by rw [hpEq]
      _=(ρ*D)*rsv:=by ring
      _=2*(Fintype.card U:ℝ)*rsv:=by rw [hsize]
  · intro w
    simp only [ordinaryAssignedSpokeProbability,Bool.false_eq_true,ite_false]
end Oberwolfach
