module

public import Oberwolfach.MarkedReferenceWeightedLoadAfterChanges

@[expose] public section
/-! Double counting for a vertex-based cycle hypergraph. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycle_fractional_vertex_incidence
    {V E C:Type} [Fintype V] [Fintype E] [Fintype C]
    (edgeAt:E→V→Prop) (edgeOf:C→E→Prop) (vertexOf:C→V→Prop) (w:C→ℝ)
    (hcycle:∀ c v,(∑ e,if edgeAt e v ∧ edgeOf c e then (1:ℝ) else 0)=
      if vertexOf c v then 2 else 0)
    (hdecomp:∀ e,(∑ c,if edgeOf c e then w c else 0)=1):
    ∀ v,2*(∑ c,if vertexOf c v then w c else 0)=∑ e,if edgeAt e v then (1:ℝ) else 0 := by
  intro v
  calc
    2*(∑ c,if vertexOf c v then w c else 0) =
        ∑ c,(∑ e,if edgeAt e v ∧ edgeOf c e then (1:ℝ) else 0)*w c := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [hcycle c v]
      split_ifs <;> simp_all <;> ring
    _ = ∑ e,∑ c,if edgeAt e v then (if edgeOf c e then w c else 0) else 0 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp_all
    _ = ∑ e,if edgeAt e v then (1:ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      by_cases h:edgeAt e v
      · simp only [h,ite_true];exact hdecomp e
      · simp [h]
theorem cycle_fractional_vertex_incidence_near_regular
    {V E C:Type} [Fintype V] [Fintype E] [Fintype C]
    (edgeAt:E→V→Prop) (edgeOf:C→E→Prop) (vertexOf:C→V→Prop) (w:C→ℝ)
    (hcycle:∀ c v,(∑ e,if edgeAt e v ∧ edgeOf c e then (1:ℝ) else 0)=
      if vertexOf c v then 2 else 0)
    (hdecomp:∀ e,(∑ c,if edgeOf c e then w c else 0)=1)
    (D η:ℝ) (hdeg:∀ v,|(∑ e,if edgeAt e v then (1:ℝ) else 0)-D|≤η):
    ∀ v,|(∑ c,if vertexOf c v then w c else 0)-D/2|≤η/2 := by
  intro v
  have hi:=cycle_fractional_vertex_incidence edgeAt edgeOf vertexOf w hcycle hdecomp v
  have hd:=hdeg v
  rw [←hi] at hd
  rcases abs_le.mp hd with ⟨hlo,hhi⟩
  apply abs_le.mpr
  constructor <;> linarith
end Oberwolfach
