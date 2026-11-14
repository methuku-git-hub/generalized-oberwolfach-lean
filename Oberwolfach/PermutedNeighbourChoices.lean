module

public import Oberwolfach.DenseCommonNeighbourBounds
public import Oberwolfach.PermutationNeighbourCounts
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Extension counts for a new label in a specified class. Its physical
head may be permuted; all roots are ambient vertices, and all used labels
are excluded in the auxiliary permutation-distance relation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def permutedNeighbourChoices {V : Type*} [Fintype V]
    (P : SimpleGraph V) (π τ : Equiv.Perm V) (b : ℕ) (A R S : Finset V) : Finset V :=
  A.filter (fun v=>(∀ x∈R,P.Adj x (τ v)) ∧ ∀ x∈S,¬PermutationClose π b x v)

theorem permutationClose_union_card {V : Type*} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (b : ℕ) (S : Finset V) :
    (S.biUnion (fun x=>Finset.univ.filter (fun v=>PermutationClose π b x v))).card≤S.card*(2*b+1) := by
  calc
    _ ≤ ∑ x∈S,(Finset.univ.filter (fun v=>PermutationClose π b x v)).card := Finset.card_biUnion_le
    _ ≤ ∑ _x∈S,(2*b+1) := by
      apply Finset.sum_le_sum
      intro x _
      simpa only [Fintype.card_subtype] using permutationClose_neighbour_card π b x
    _ = _ := by simp

theorem permutedNeighbourChoices_card_lower {V : Type*} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V) (π τ : Equiv.Perm V) (b : ℕ) (A R S : Finset V)
    (α : ℝ) (hα1 : α≤1) (hR : R.card≤2)
    (hdegree : ∀ x∈R,(1/2+α/2)*A.card≤((P.neighborFinset x∩A.image τ).card:ℝ)) :
    α*A.card-(S.card:ℝ)*(2*(b:ℝ)+1)≤(permutedNeighbourChoices P π τ b A R S).card := by
  let N := fun x=>Finset.univ.filter (fun v=>P.Adj x (τ v))
  have hdeg (x : V) (hx : x∈R) : (1/2+α/2)*A.card≤((A∩N x).card:ℝ) := by
    have he : A∩N x=A.filter (fun v=>P.Adj x (τ v)) := by ext v;simp [N]
    rw [he,permutation_neighbour_filter_card]
    exact hdegree x hx
  have hc := common_neighbour_card_lower A R N (1/2+α/2) hdeg
  have hR' : (R.card:ℝ)≤2 := by exact_mod_cast hR
  have hco : α≤1-(R.card:ℝ)*(1-(1/2+α/2)) := by
    have hh := mul_le_mul_of_nonneg_right hR' (show 0≤1-(1/2+α/2) by linarith)
    nlinarith only [hh]
  let D := S.biUnion (fun x=>Finset.univ.filter (fun v=>PermutationClose π b x v))
  have hD : (D.card:ℝ)≤(S.card:ℝ)*(2*(b:ℝ)+1) := by
    exact_mod_cast permutationClose_union_card π b S
  have he : permutedNeighbourChoices P π τ b A R S=common A R N\D := by
    ext v
    simp only [permutedNeighbourChoices,common,N,D,Finset.mem_filter,Finset.mem_sdiff,
      Finset.mem_univ,true_and,Finset.mem_biUnion,not_exists,not_and]
    tauto
  rw [he]
  have hl : ((common A R N).card:ℝ)≤(common A R N\D).card+D.card := by
    exact_mod_cast (Finset.card_le_card_sdiff_add_card (s:=common A R N) (t:=D))
  have hm := mul_le_mul_of_nonneg_right hco (Nat.cast_nonneg A.card : (0:ℝ)≤A.card)
  linarith only [hc,hD,hl,hm]

end Oberwolfach
