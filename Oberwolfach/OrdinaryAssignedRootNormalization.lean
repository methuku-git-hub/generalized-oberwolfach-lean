module

public import Oberwolfach.OrdinaryAssignedApproximateDensityBounds

@[expose] public section
/-! The actual retained frequencies normalize both ordinary spoke-root
loads and physical rim-root loads in the ordinary construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_assigned_root_normalization
    {n:ℕ} (hn:0<n) {U:Type} [Fintype U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv θ c ρ D:ℝ) (d:ℕ) (hd:2≤d)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hθ:0<θ) (hθ1:θ≤1/100) (hc:8≤c)
    (hda:1/θ≤d) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D) (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (F w) K=some i₀):
    let a:=ordinaryAssignedLongWeight F hF K θ c
    let b:=ordinaryAssignedShortWeight F hF K i₀ rsv θ c
    let η:=fun w i=>ordinaryAssignedFrequencyCoefficient F hF K i₀ rsv θ c w i
    let p:=(∑w,(a w+b w))/D;
    (∀w,(c-1)*a w/b w+∑i,η w i=1) ∧
    (∑ w : U, (c*a w+b w*(∑i,η w i)))/(D*p)=1 :=by
  intro a b η p
  have hdens:=ordinary_assigned_approximate_density_bounds hn F hF K hK i₀ rsv θ c ρ D d hd
    hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize S hS hsclass hclass
  have hp:0<p:=lt_of_lt_of_le hdens.1 hdens.2.1
  have hreserve:=ordinary_class_reservation hn F hF S hS K hK i₀ rsv hsclass hclass
  have hbal (u:U):(∑i,η u i)*b u+(c-1)*a u=b u :=by
    have hh:=ordinary_factor_frequency_weight_allocation hn (F u) (hF u) K hK i₀ rsv θ c
      hs0 hs1 hθ.le hθ1 hc (hreserve u)
    have h:=hh.2.2
    simpa only [a,b,η,ordinaryAssignedFrequencyCoefficient,ordinaryAssignedKeptFraction,
      ordinaryAssignedShortWeight,ordinaryAssignedLongWeight,ordinaryAssignedFraction] using h
  constructor
  · intro u
    have hb:0<b u:=lt_of_lt_of_le hdens.1 (hdens.2.2.2.1 u).1
    have hh:=hbal u
    field_simp
    nlinarith
  · have hsum:(∑ u : U, (c*a u+b u*(∑i,η u i)))=∑u,(a u+b u) :=by
      apply Finset.sum_congr rfl
      intro u _
      have hh:=hbal u
      nlinarith
    rw [hsum]
    have heq:(∑u,(a u+b u))=D*p:=by dsimp [p];field_simp
    rw [heq]
    exact div_self (ne_of_gt (mul_pos hD hp))
end Oberwolfach
