module

public import Oberwolfach.UniformIncomingFraction
public import Oberwolfach.BipartiteOneSidedRoundingSupport

@[expose] public section
/-! Uniform fractional choices at the heads can be rounded without selecting
any ineligible edge, while the integer head demands are exact. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {X Y E : Type} [Fintype X] [Fintype Y] [Fintype E]

theorem uniform_incoming_rounding
    (tail : E→X) (head : E→Y) (eligible : E→Prop) (t : Y→ℕ)
    (ht : ∀ y, t y ≤ (eligibleIncoming head eligible y).card) :
    ∃ D : E→Bool,
      (∀ e, D e=true → eligible e) ∧
      (∀ y, (∑ e, if head e=y ∧ D e=true then (1:ℕ) else 0) = t y) ∧
      (∀ x, (∑ e, if tail e=x ∧ D e=true then (1:ℕ) else 0) ≤
        ⌈∑ e, if tail e=x then uniformIncomingWeight head eligible t e else 0⌉₊) := by
  obtain ⟨D,hrow,hcol,hsupport⟩ := bipartite_rounding_with_tail_ceilings_support tail head t
    (uniformIncomingWeight head eligible t) (uniform_incoming_weight_bounds head eligible t ht)
    (uniform_incoming_weight_columns head eligible t ht)
  refine ⟨D, ?_, hcol, hrow⟩
  intro e he
  by_contra hn
  have hz : uniformIncomingWeight head eligible t e = 0 := by simp [uniformIncomingWeight,hn]
  have hf := hsupport e hz
  rw [he] at hf
  cases hf
theorem uniform_incoming_weight_upper
    (head : E→Y) (eligible : E→Prop) (t : Y→ℕ) (tau rho : ℝ)
    (htau : 0≤tau) (hrho : 0<rho)
    (ht : ∀ y, (t y:ℝ)≤tau)
    (hsize : ∀ y, rho≤((eligibleIncoming head eligible y).card:ℝ)) (e : E) :
    uniformIncomingWeight head eligible t e ≤ tau/rho := by
  unfold uniformIncomingWeight
  split_ifs with he
  · exact div_le_div₀ htau (ht (head e)) hrho (hsize (head e))
  · exact div_nonneg htau hrho.le

theorem uniform_incoming_rounding_bounded
    (tail : E→X) (head : E→Y) (eligible : E→Prop) (t : Y→ℕ)
    (ht : ∀ y, t y ≤ (eligibleIncoming head eligible y).card)
    (tau rho : ℝ) (M : ℕ) (htau : 0≤tau) (hrho : 0<rho)
    (htauBound : ∀ y, (t y:ℝ)≤tau)
    (hsize : ∀ y, rho≤((eligibleIncoming head eligible y).card:ℝ))
    (hdegree : ∀ x, (Finset.univ.filter (fun e=>tail e=x)).card≤M) :
    ∃ D : E→Bool,
      (∀ e, D e=true → eligible e) ∧
      (∀ y, (∑ e, if head e=y ∧ D e=true then (1:ℕ) else 0) = t y) ∧
      (∀ x, (∑ e, if tail e=x ∧ D e=true then (1:ℕ) else 0) ≤ ⌈(M:ℝ)*(tau/rho)⌉₊) := by
  obtain ⟨D,hD,hheads,htails⟩ := uniform_incoming_rounding tail head eligible t ht
  refine ⟨D,hD,hheads,?_⟩
  intro x
  apply (htails x).trans
  apply Nat.ceil_mono
  let S := Finset.univ.filter (fun e=>tail e=x)
  have hc : 0≤tau/rho := div_nonneg htau hrho.le
  calc
    (∑ e, if tail e=x then uniformIncomingWeight head eligible t e else 0) =
        ∑ e∈S, uniformIncomingWeight head eligible t e := by
          simp only [S,Finset.sum_filter]
    _ ≤ ∑ _e∈S, tau/rho := by
      apply Finset.sum_le_sum
      intro e _
      exact uniform_incoming_weight_upper head eligible t tau rho htau hrho htauBound hsize e
    _ = (S.card:ℝ)*(tau/rho) := by simp
    _ ≤ (M:ℝ)*(tau/rho) := by
      apply mul_le_mul_of_nonneg_right _ hc
      exact_mod_cast hdegree x
end Oberwolfach
