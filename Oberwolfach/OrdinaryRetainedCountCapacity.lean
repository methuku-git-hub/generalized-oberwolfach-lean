module

public import Oberwolfach.OrdinaryRetainedAvailableComponents
public import Oberwolfach.OrdinaryRetainedTestRealLength
public import Oberwolfach.RetainedWheelComponentCapacity

@[expose] public section
/-! Relative control of a retained wheel count supplies strictly enough
unreserved factor components of the corresponding actual length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_retained_count_capacity
    {n K:ℕ} (hn:0<n) {U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
    (hK:0<K) (i₀:Fin K) (s θ lam:ℝ) (hs0:0≤s) (hθ:0<θ) (hlam:lam<θ)
    (z:OrdinaryAssignedRetainedHubTest F hF i₀ s θ)
    (C:Finset (F z.val.2).ConnectedComponent)
    (hC:∀c∈C,Fintype.card c=i₀.val+1)
    (hreserve:((i₀.val+1:ℕ):ℝ)*(C.card:ℝ)=s*n)
    (count:ℕ)
    (hcount:|((longPaddedSeedExponent z.val.1+2:ℕ):ℝ)*count-
      (1-θ)*ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1*n|≤
      lam*ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1*n):
    let T:=Finset.univ.filter (fun c:(F z.val.2).ConnectedComponent=>Fintype.card c=z.val.1.val+1)
    count<(T\C).card :=by
  intro T
  have hlength:longPaddedSeedExponent z.val.1+2=z.val.1.val+1:=
    (ordinary_retained_test_real_length hn F hF Allowed hAllowed hK i₀ s θ hs0 hθ z).2.1
  have hK':0<(K:ℝ):=by exact_mod_cast hK
  have hf:0<ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1:=
    (show 0<θ/(100*(K:ℝ)) by positivity).trans_le z.property
  have havail:=ordinary_retained_available_components hn F hF hK i₀ s θ hθ z.val.2 z.val.1 C hC hreserve z.property
  dsimp only at havail
  have hupper:= (abs_le.mp hcount).2
  rw [hlength] at hupper
  apply retained_wheel_component_capacity (z.val.1.val+1) count (T\C).card
    (ordinaryAssignedKeptFraction F hF K i₀ s θ z.val.2 z.val.1) n θ lam (by omega) hf (by exact_mod_cast hn) hlam
  · nlinarith
  · exact le_of_eq havail
end Oberwolfach
