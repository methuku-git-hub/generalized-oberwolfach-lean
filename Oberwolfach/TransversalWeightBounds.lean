module

public import Oberwolfach.PrescribedVertexCounts
public import Oberwolfach.FractionalDecompositions

@[expose] public section

/-! A graph event forcing specified class vertices has the corresponding
finite counting bound, including incompatible prescriptions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem transversal_graph_weight_bound {I X V : Type*}
    [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq V]
    (cl : V → I) (val : V → X)
    (hinj : Function.Injective (fun v => (cl v, val v)))
    (C : (I → X) → SimpleGraph V) (hC : Function.Injective C)
    (w : SimpleGraph V → ℝ) (hw : ∀ H, 0 ≤ w H)
    (hs : ∀ H, 0 < w H → H ∈ Set.range C)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ f, w (C f) ≤ M)
    (S : Finset V) (E : SimpleGraph V → Prop)
    (hE : ∀ f, E (C f) → ∀ v ∈ S, f (cl v) = val v) :
    (∑ H, if E H then w H else 0) ≤
      (Fintype.card X : ℝ) ^ (Fintype.card I - S.card) * M := by
  classical
  have hsum : (∑ f, if E (C f) then w (C f) else 0) =
      ∑ H, if E H then w H else 0 := by
    apply Fintype.sum_of_injective C hC
    · intro H hH
      have hz : w H = 0 := by
        by_contra hn
        exact hH (hs H (lt_of_le_of_ne (hw H) (Ne.symm hn)))
      simp only [hz, ite_self]
    · intro f; rfl
  rw [← hsum]
  calc
    _ ≤ ∑ f, if (∀ v ∈ S, f (cl v) = val v) then w (C f) else 0 := by
      apply Finset.sum_le_sum
      intro f _
      by_cases he : E (C f)
      · rw [if_pos he, if_pos (hE f he)]
      · simp only [he, ite_false]
        split_ifs
        · exact hw _
        · exact le_refl _
    _ ≤ _ := by
      convert prescribedVertices_weight_le S cl val hinj (fun f => w (C f)) M hM hb using 1
      apply Finset.sum_congr rfl
      intro f _
      split_ifs <;> rfl

theorem normalized_transversal_power (n B : ℝ) (d s : ℕ)
    (hn : n ≠ 0) (hs : 2 ≤ s) (hsd : s ≤ d) :
    n ^ (d - s) * (B / n ^ (d - 2)) = B / n ^ (s - 2) := by
  have he : d - 2 = (d - s) + (s - 2) := by omega
  rw [he, pow_add]
  field_simp

end Oberwolfach
