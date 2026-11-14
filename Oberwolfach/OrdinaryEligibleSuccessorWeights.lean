module

public import Oberwolfach.OrdinaryEligibleHost
public import Oberwolfach.SuccessorSequenceWeights
public import Oberwolfach.DivisibilityRepairScales

@[expose] public section
/-! Choose successor weights on the physically eligible subgraph using the
original host's positive degree margin and near-regularity. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) eligibleWeightFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_eligible_successor_weights
    (k:ℕ) (α τ:ℝ) (hα:0<α) (hτ:0<τ):
    ∃δ:ℝ,0<δ ∧ ∀d:ℕ,∃N:ℕ,∀n:ℕ,N≤n→
    ∀(P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (D:ℝ),
    (n:ℝ)/2≤D→D≤2*n→
    (∀v,|(P.degree v:ℝ)-D|≤δ*n)→
    (∀v,(successorCycleRatio k+α)*n≤(P.degree v:ℝ))→
    ∃weight:(Fin ((k+2)*2)→Fin n)→ℝ,
      SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/2)) (successorWeightUpper k (α/2)) weight :=by
  obtain ⟨ε,hε,hweights⟩:=successor_sequence_weight_existence k (α/2) (by positivity) τ hτ
  refine ⟨ε/2,by positivity,?_⟩
  intro d
  obtain ⟨N₀,hN₀⟩:=hweights (3*d)
  obtain ⟨N₁,hN₁⟩:=eventually_constant_le_linear ((6*d+4:ℕ):ℝ) (min (ε/2) (α/2)) (by positivity)
  refine ⟨max (max N₀ N₁) 1,?_⟩
  intro n hn P π D hDlo hDhi hnear hmin
  have hn0:0<n:=by omega
  letI:Nonempty (Fin n):=⟨⟨0,hn0⟩⟩
  have hsmall:=hN₁ n (by omega)
  have hsmallε:((6*d+4:ℕ):ℝ)≤(ε/2)*n:=hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
  have hsmallα:((6*d+4:ℕ):ℝ)≤(α/2)*n:=hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
  have hnear':∀v,|((ordinaryEligibleHost P π d).degree v:ℝ)-D|≤ε*n:=by
    intro v
    have hd:=ordinary_eligible_host_degree P π d v
    have hlo:((P.degree v:ℝ))≤((ordinaryEligibleHost P π d).degree v:ℝ)+((6*d+4:ℕ):ℝ):=by exact_mod_cast hd.2
    have hhi:((ordinaryEligibleHost P π d).degree v:ℝ)≤P.degree v:=by exact_mod_cast hd.1
    have hh:=abs_le.mp (hnear v)
    apply abs_le.mpr
    constructor <;> linarith
  have hmin':∀v,(successorCycleRatio k+α/2)*(n:ℝ)≤((ordinaryEligibleHost P π d).degree v:ℝ):=by
    intro v
    have hd:=ordinary_eligible_host_degree P π d v
    have hlo:((P.degree v:ℝ))≤((ordinaryEligibleHost P π d).degree v:ℝ)+((6*d+4:ℕ):ℝ):=by exact_mod_cast hd.2
    have hh:=hmin v
    nlinarith
  apply hN₀ (Fin n) (by simpa using (show N₀≤n by omega)) (ordinaryEligibleHost P π d) π D
    (by simpa using hDlo) (by simpa using hDhi)
  · simpa only [Fintype.card_fin] using hnear'
  · simpa only [Fintype.card_fin] using hmin'
end Oberwolfach
