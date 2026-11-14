module

public import Oberwolfach.CommonEvents

@[expose] public section

/-! Exact weighted incidence sums for finite hypergraphs with edge
identifiers. Parallel identifiers are counted separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]

def hypergraphWeightedDegree (R : E → Finset V) (w : E → ℝ) (v : V) : ℝ :=
  ∑ e,if v∈R e then w e else 0

theorem hypergraphWeightedDegree_nonneg (R : E → Finset V) (w : E → ℝ)
    (hw : ∀ e,0≤w e) (v : V) : 0≤hypergraphWeightedDegree R w v := by
  unfold hypergraphWeightedDegree
  apply Finset.sum_nonneg
  intro e _
  split_ifs <;> first | exact hw e | exact le_refl _

theorem hypergraphWeightedDegree_sum (R : E → Finset V) (w : E → ℝ) :
    (∑ v,hypergraphWeightedDegree R w v)=∑ e,(R e).card*w e := by
  unfold hypergraphWeightedDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [← Finset.sum_filter]
  have he : Finset.univ.filter (fun v=>v∈R e)=R e := by ext;simp
  rw [he,Finset.sum_const,nsmul_eq_mul]

theorem hypergraphWeightedDegree_sum_uniform (R : E → Finset V) (w : E → ℝ)
    (k : ℕ) (hR : ∀ e,(R e).card=k) :
    (∑ v,hypergraphWeightedDegree R w v)=(k:ℝ)*∑ e,w e := by
  rw [hypergraphWeightedDegree_sum]
  simp only [hR,← Finset.mul_sum]

theorem hypergraphWeightedDegree_square_sum (R : E → Finset V) (w : E → ℝ)
    (hw : ∀ e,0≤w e) (k : ℕ) (hR : ∀ e,(R e).card=k)
    (D : ℝ) (hD : ∀ v,hypergraphWeightedDegree R w v≤D) :
    (∑ v,(hypergraphWeightedDegree R w v)^2)≤D*k*∑ e,w e := by
  calc
    _ ≤ ∑ v,D*hypergraphWeightedDegree R w v := by
      apply Finset.sum_le_sum
      intro v _
      have h0 := hypergraphWeightedDegree_nonneg R w hw v
      have hh := mul_le_mul_of_nonneg_right (hD v) h0
      simpa only [pow_two] using hh
    _ = _ := by rw [← Finset.mul_sum,hypergraphWeightedDegree_sum_uniform R w k hR];ring

theorem hypergraphWeightedDegree_square_sum_pos (R : E → Finset V) (w : E → ℝ)
    (hw : ∀ e,0≤w e) (k : ℕ) (hk : 0<k) (hR : ∀ e,(R e).card=k)
    (hW : 0<∑ e,w e) : 0<∑ v,(hypergraphWeightedDegree R w v)^2 := by
  have hs : 0<∑ v,hypergraphWeightedDegree R w v := by
    rw [hypergraphWeightedDegree_sum_uniform R w k hR]
    exact mul_pos (Nat.cast_pos.mpr hk) hW
  obtain ⟨v,hv,hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun v _=>hypergraphWeightedDegree_nonneg R w hw v)).mp hs
  exact (sq_pos_of_pos hpos).trans_le (Finset.single_le_sum (fun v _=>sq_nonneg _) hv)

theorem hypergraphWeightedDegree_card_bound (R : E → Finset V) (w : E → ℝ)
    (b : ℝ) (hb : ∀ e,w e≤b) (v : V) :
    hypergraphWeightedDegree R w v≤b*(Finset.univ.filter (fun e=>v∈R e)).card := by
  unfold hypergraphWeightedDegree
  calc
    _ ≤ ∑ e,if v∈R e then b else 0 := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs <;> first | exact hb e | exact le_refl _
    _ = _ := by rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul];ring

end Oberwolfach
