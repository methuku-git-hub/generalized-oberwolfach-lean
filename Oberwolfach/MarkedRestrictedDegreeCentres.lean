module

public import Oberwolfach.MarkedRestrictedDegreeCounts
public import Oberwolfach.MarkedLocalNeighbourGraphs

@[expose] public section

/-! Exact parent centres and the deterministic cost of removing
permutation-close auxiliary pairs on a restricted domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [LinearOrder V]

def markedParentDegreeDomain (P : SimpleGraph V) (π : Equiv.Perm V)
    (mark incoming : Bool) (x : V) (A : Finset V) : Finset V :=
  A.filter (fun y=>P.Adj (markedDegreeEndpoints π mark incoming x y).1
    (markedDegreeEndpoints π mark incoming x y).2)

theorem markedParentDegreeDomain_card (P : SimpleGraph V) (π : Equiv.Perm V)
    (mark incoming : Bool) (x : V) (A : Finset V) (hInv : ∀ y,π y∈A ↔ y∈A) :
    (markedParentDegreeDomain P π mark incoming x A).card=
      (P.neighborFinset (if mark && incoming then π x else x)∩A).card := by
  have hf (v : V) : A.filter (P.Adj v)=P.neighborFinset v∩A := by ext y;simp [and_comm]
  cases mark <;> cases incoming
  · simpa [markedParentDegreeDomain,markedDegreeEndpoints,Bool.false_eq_true,ite_false,Bool.and_false] using congrArg Finset.card (hf x)
  · simpa [markedParentDegreeDomain,markedDegreeEndpoints,P.adj_comm] using congrArg Finset.card (hf x)
  · simpa [markedParentDegreeDomain,markedDegreeEndpoints,invariant_finset_image π A hInv] using permutation_neighbour_filter_card P π A x
  · simpa [markedParentDegreeDomain,markedDegreeEndpoints,P.adj_comm] using congrArg Finset.card (hf (π x))

theorem markedDegreeDomain_card_loss (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (mark incoming : Bool) (x : V) (A : Finset V) :
    (markedDegreeDomain P π b mark incoming x A).card≤(markedParentDegreeDomain P π mark incoming x A).card ∧
    (markedParentDegreeDomain P π mark incoming x A).card≤(markedDegreeDomain P π b mark incoming x A).card+(2*b+1) := by
  have hsub : markedDegreeDomain P π b mark incoming x A⊆markedParentDegreeDomain P π mark incoming x A := by
    intro y hy
    obtain ⟨hy,hc,hp⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hy,hp⟩
  refine ⟨Finset.card_le_card hsub,?_⟩
  let C := Finset.univ.filter (PermutationClose π b x)
  have hC : C.card≤2*b+1 := by
    simpa only [Fintype.card_subtype] using permutationClose_neighbour_card π b x
  have hcover : markedParentDegreeDomain P π mark incoming x A⊆markedDegreeDomain P π b mark incoming x A∪C := by
    intro y hy
    obtain ⟨hy,hp⟩ := Finset.mem_filter.mp hy
    by_cases hc : PermutationClose π b x y
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy,hc,hp⟩)
  exact (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add_left hC _))

theorem markedRestrictedDegree_parent_error (P : SimpleGraph V) (π : Equiv.Perm V) (b : ℕ)
    (σ : Sym2 V→Option (Bool×Bool)) (mark incoming : Bool) (x : V) (A : Finset V)
    (hInv : ∀ y,π y∈A ↔ y∈A) (p t : ℝ) (hp : 0≤p) (hp1 : p≤1)
    (he : |(markedRestrictedDegree P π b σ mark incoming x A:ℝ)-p*(markedDegreeDomain P π b mark incoming x A).card|≤t) :
    |(markedRestrictedDegree P π b σ mark incoming x A:ℝ)-
      p*(P.neighborFinset (if mark && incoming then π x else x)∩A).card|≤t+(2*(b:ℝ)+1) := by
  have hh := markedDegreeDomain_card_loss P π b mark incoming x A
  have hcard := markedParentDegreeDomain_card P π mark incoming x A hInv
  have hlo : ((markedDegreeDomain P π b mark incoming x A).card:ℝ)≤
      (P.neighborFinset (if mark && incoming then π x else x)∩A).card := by exact_mod_cast hcard ▸ hh.1
  have hhi : ((P.neighborFinset (if mark && incoming then π x else x)∩A).card:ℝ)≤
      (markedDegreeDomain P π b mark incoming x A).card+(2*(b:ℝ)+1) := by exact_mod_cast hcard ▸ hh.2
  have hdiff : |p*(markedDegreeDomain P π b mark incoming x A).card-
      p*(P.neighborFinset (if mark && incoming then π x else x)∩A).card|≤2*(b:ℝ)+1 := by
    rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (mul_le_mul_of_nonneg_left hlo hp))]
    nlinarith only [mul_le_mul_of_nonneg_left hhi hp,mul_le_mul_of_nonneg_right hp1 (show 0≤2*(b:ℝ)+1 by positivity)]
  exact (abs_sub_le _ (p*(markedDegreeDomain P π b mark incoming x A).card) _).trans (add_le_add he hdiff)

end Oberwolfach
