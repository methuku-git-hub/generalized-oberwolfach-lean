module

public import Oberwolfach.UniformResourceCounts
public import Oberwolfach.HypergraphWeightMoments
public import Oberwolfach.OrdinaryCycleConflictLoss

@[expose] public section

/-! Pair-weight bounds and the exact loss caused by removing vertices.
The weights are the supplied weights on surviving indexed cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

theorem uniform_resource_pair_weight (R : C → Finset V) (c J : ℕ) (hc : 2 ≤ c)
    (hR : ∀ C₀,(R C₀).card=c) (hJ : ∀ Y : Finset V,Fintype.card {C₀ : C // R C₀=Y} ≤ J)
    (w : C → ℝ) (B k : ℝ) (hB : 0 ≤ B) (hk : 0 < k)
    (hn : (Fintype.card V:ℝ)=c*k) (hw : ∀ C₀,w C₀ ≤ B/k^(c-1))
    (u v : V) (huv : u≠v) :
    (∑ C₀,if u∈R C₀ ∧ v∈R C₀ then w C₀ else 0) ≤ B*J*(c:ℝ)^(c-2)/k := by
  have hcount := uniform_resources_pair_count R c J hc hR hJ u v huv
  have hcountR : (Fintype.card {C₀ : C // u∈R C₀ ∧ v∈R C₀}:ℝ) ≤ J*((c:ℝ)*k)^(c-2) := by
    rw [← hn];exact_mod_cast hcount
  calc
    _ ≤ ∑ C₀,if u∈R C₀ ∧ v∈R C₀ then B/k^(c-1) else 0 := by
      apply Finset.sum_le_sum
      intro C₀ _;split_ifs <;> first | exact hw C₀ | exact le_refl _
    _ = (Fintype.card {C₀ : C // u∈R C₀ ∧ v∈R C₀}:ℝ)*(B/k^(c-1)) := by
      simp only [Fintype.card_subtype,← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    _ ≤ (J*((c:ℝ)*k)^(c-2))*(B/k^(c-1)) := mul_le_mul_of_nonneg_right hcountR (by positivity)
    _ = _ := by
      have he : c-1=(c-2)+1 := by omega
      rw [he,pow_succ,mul_pow]
      field_simp
      <;> ring

end Oberwolfach
