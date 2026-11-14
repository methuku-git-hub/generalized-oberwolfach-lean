module

public import Oberwolfach.PermutationMatrixDegrees
public import Oberwolfach.DirectedRelationDeletion
public import Oberwolfach.RandomOrientation

@[expose] public section

/-! Deleting permutation-close arcs from an already realised directed graph
loses at most 4b+2 middle vertices, without a sampling-density factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V : Type} [Fintype V] [DecidableEq V]

theorem eligibleTwoPathCount_eq_univ (P : SimpleGraph V) (M : V→V→ℕ)
    (hM : ∀ x y,0<M x y→P.Adj x y) (x y : V) :
    eligibleTwoPathCount P M x y=(Finset.univ.filter (fun z=>0<M x z ∧ 0<M z y)).card := by
  unfold eligibleTwoPathCount
  congr 1
  ext z
  simp only [Finset.mem_filter,Finset.mem_inter,SimpleGraph.mem_neighborFinset,
    Finset.mem_univ,true_and]
  exact ⟨fun h=>h.2,fun h=>⟨⟨hM x z h.1,(hM z y h.2).symm⟩,h⟩⟩

theorem permutationSeparatedMatrix_two_step_loss (π : Equiv.Perm V) (b : ℕ)
    (M : V→V→ℕ) (x y : V) :
    |((Finset.univ.filter (fun z=>0<permutationSeparatedMatrix π b M x z ∧
          0<permutationSeparatedMatrix π b M z y)).card:ℝ)-
       (Finset.univ.filter (fun z=>0<M x z ∧ 0<M z y)).card|≤2*(2*(b:ℝ)+1) := by
  have hsub (x y : V) : 0<permutationSeparatedMatrix π b M x y → 0<M x y := by
    simp only [permutationSeparatedMatrix]
    split_ifs <;> omega
  have hrow (x : V) : (∑ z,bipAdj (fun x z=>0<M x z ∧
      ¬0<permutationSeparatedMatrix π b M x z) x z)≤2*(b:ℝ)+1 := by
    calc
      _ ≤ ∑ z,if PermutationClose π b x z then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro z _
        by_cases h : PermutationClose π b x z
        · simp only [h,ite_true];exact bipAdj_le_one _ _ _
        · simp only [bipAdj,permutationSeparatedMatrix,if_neg h,and_not_self,ite_false,le_refl]
      _ ≤ _ := by
        have h := permutationClose_neighbour_card π b x
        simp only [Fintype.card_subtype,Finset.card_filter] at h
        exact_mod_cast h
  have hcol : (∑ z,bipAdj (fun z y=>0<M z y ∧
      ¬0<permutationSeparatedMatrix π b M z y) z y)≤2*(b:ℝ)+1 := by
    calc
      _ ≤ ∑ z,if PermutationClose π b y z then (1:ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro z _
        by_cases h : PermutationClose π b z y
        · simp only [← permutationClose_symm π b z y,h,ite_true];exact bipAdj_le_one _ _ _
        · simp only [bipAdj,permutationSeparatedMatrix,if_neg h,← permutationClose_symm π b z y,if_neg h,and_not_self,ite_false,le_refl]
      _ ≤ _ := by
        have h := permutationClose_neighbour_card π b y
        simp only [Fintype.card_subtype,Finset.card_filter] at h
        exact_mod_cast h
  convert directed_two_step_deletion (fun x y=>0<M x y)
    (fun x y=>0<permutationSeparatedMatrix π b M x y) hsub x y (2*b+1) (hrow x) hcol using 1 <;> congr!

end Oberwolfach
