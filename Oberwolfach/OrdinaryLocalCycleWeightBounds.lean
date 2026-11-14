module

public import Oberwolfach.OrdinaryLocalLoads
public import Oberwolfach.NormalizedCycleWeightBounds

@[expose] public section
/-! Two-sided bounds on the original parent weights restricted to local cycles. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
variable {V:Type} [Fintype V] [DecidableEq V] {r:ℕ}
theorem ordinary_local_cycle_weight_bounds (P Q F:SimpleGraph V) (T:Finset V) (hQP:Q≤P)
    (weight:OrdinaryCycle P r→ℝ) (D c cmin a b:ℝ)
    (hr:2≤r) (hn:0<(Fintype.card V:ℝ))
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hcmin:0<cmin) (hclo:cmin≤c) (hchi:c≤1) (ha:0≤a) (hb:0≤b)
    (hwlo:∀ C,a/(Fintype.card V:ℝ)^(r-2)≤weight C)
    (hwhi:∀ C,weight C≤b/(Fintype.card V:ℝ)^(r-2)):
    ∀ C:LocalOrdinaryCycle Q F T r,
      a/(Fintype.card V:ℝ)^(r-1)≤weight (localOrdinaryParent hQP C)/(D/2)/c ∧
      weight (localOrdinaryParent hQP C)/(D/2)/c≤(4*b/cmin)/(Fintype.card V:ℝ)^(r-1) := by
  intro C
  exact normalized_cycle_weight_bounds r hr (Fintype.card V) D c cmin a b
    (weight (localOrdinaryParent hQP C)) hn hDlo hDhi hcmin hclo hchi ha hb
    (hwlo (localOrdinaryParent hQP C)) (hwhi (localOrdinaryParent hQP C))
end Oberwolfach
