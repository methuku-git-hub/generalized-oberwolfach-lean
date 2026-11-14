module

public import Oberwolfach.NibbleColourCounts

@[expose] public section

/-! Exact counting identities for the colours left after a tentative
round. Rejection in a clique is equivalent to rejection of every vertex
of that clique assigned the same colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem clique_assigned_rejected_iff
    {V C : Type*} (G : SimpleGraph V) (T : Finset V)
    (hT : ∀ u∈T,∀ v∈T,u≠v → G.Adj u v) (σ : V → C×Bool) (c : C) :
    (colourAssignedIn T σ c ∧ ¬colourRejectedIn G T σ c) ↔
      ∃ v∈T,coinRetainedColour G σ v=some c := by
  constructor
  · rintro ⟨⟨v,hv,hc⟩,hn⟩
    refine ⟨v,hv,(coinRetainedColour_eq_some G σ v c).mpr ⟨hc,?_⟩⟩
    by_contra hbad
    exact hn ⟨v,hv,hc,hbad⟩
  · rintro ⟨v,hv,hkeep⟩
    obtain ⟨hc,hsurv⟩ := (coinRetainedColour_eq_some G σ v c).mp hkeep
    refine ⟨⟨v,hv,hc⟩,?_⟩
    rintro ⟨u,hu,huc,hbad⟩
    by_cases he : u=v
    · subst u
      exact hbad hsurv
    · exact hsurv.2 u (hT v hv u hu (Ne.symm he)) (huc.trans hc.symm)

def nibbleAvailableColours {V C J : Type*} (G : SimpleGraph V)
    (Q : Finset J) (T : J → Finset V) (L : Finset C) (σ : V → C×Bool) : Finset C :=
  L.filter (fun c=>∀ j∈Q,∀ v∈T j,coinRetainedColour G σ v≠some c)

theorem nibbleAvailableColours_mem_iff
    {V C J : Type*} (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V)
    (hT : ∀ j∈Q,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (L : Finset C) (σ : V → C×Bool) (c : C) :
    c∈nibbleAvailableColours G Q T L σ ↔ c∈L ∧
      (assignedSetIndices Q T σ c).card=(rejectedSetIndices G Q T σ c).card := by
  classical
  have hsub := rejectedSetIndices_subset_assigned G Q T σ c
  constructor
  · intro hc
    obtain ⟨hc,hno⟩ := Finset.mem_filter.mp hc
    refine ⟨hc,?_⟩
    apply congrArg Finset.card
    apply Finset.Subset.antisymm _ hsub
    intro j hj
    obtain ⟨hj,ha⟩ := Finset.mem_filter.mp hj
    refine Finset.mem_filter.mpr ⟨hj,?_⟩
    by_contra hn
    obtain ⟨v,hv,hkeep⟩ := (clique_assigned_rejected_iff G (T j) (hT j hj) σ c).mp ⟨ha,hn⟩
    exact hno j hj v hv hkeep
  · rintro ⟨hc,hcard⟩
    have he := Finset.eq_of_subset_of_card_le hsub hcard.le
    apply Finset.mem_filter.mpr
    refine ⟨hc,?_⟩
    intro j hj v hv hkeep
    obtain ⟨ha,hn⟩ := (clique_assigned_rejected_iff G (T j) (hT j hj) σ c).mpr ⟨v,hv,hkeep⟩
    have hja : j∈assignedSetIndices Q T σ c := Finset.mem_filter.mpr ⟨hj,ha⟩
    have hjb : j∈rejectedSetIndices G Q T σ c := he.symm ▸ hja
    exact hn (Finset.mem_filter.mp hjb).2

theorem threshold_diagonal_sum {A B k : ℕ} (hB : B≤A) (hA : A≤k) :
    (∑ a∈Finset.range (k+1),
      ((if a≤A ∧ a≤B then (1 : ℝ) else 0)-
        (if a+1≤A ∧ a≤B then (1 : ℝ) else 0)))=
      if A=B then 1 else 0 := by
  have hp (a : ℕ) :
      ((if a≤A ∧ a≤B then (1 : ℝ) else 0)-
        (if a+1≤A ∧ a≤B then (1 : ℝ) else 0))=
        if A=B ∧ a=A then 1 else 0 := by
    by_cases h₁ : a≤A <;> by_cases h₂ : a≤B <;>
      by_cases h₃ : a+1≤A <;> by_cases h₄ : A=B ∧ a=A <;>
        simp only [h₁,h₂,h₃,h₄,true_and,false_and,and_true,and_false,
          ite_true,ite_false] <;> try norm_num <;> omega
  simp_rw [hp]
  by_cases he : A=B
  · subst B
    simp [Finset.mem_range.mpr (Nat.lt_succ_of_le hA)]
  · simp [he]

theorem nibbleAvailableColours_card
    {V C J : Type*} (G : SimpleGraph V) (Q : Finset J) (T : J → Finset V)
    (hT : ∀ j∈Q,∀ u∈T j,∀ v∈T j,u≠v → G.Adj u v)
    (L : Finset C) (σ : V → C×Bool) :
    ((nibbleAvailableColours G Q T L σ).card : ℝ)=
      ∑ a∈Finset.range (Q.card+1),
        (nibbleColourCount G Q T L a a σ-nibbleColourCount G Q T L (a+1) a σ) := by
  classical
  have hcard : ((nibbleAvailableColours G Q T L σ).card : ℝ)=
      ∑ c∈L,if (assignedSetIndices Q T σ c).card=
        (rejectedSetIndices G Q T σ c).card then (1 : ℝ) else 0 := by
    rw [Finset.sum_boole]
    apply congrArg (fun n : ℕ=>(n : ℝ))
    apply congrArg Finset.card
    ext c
    simp only [nibbleAvailableColours_mem_iff G Q T hT,Finset.mem_filter]
  rw [hcard]
  have hc (a b : ℕ) : nibbleColourCount G Q T L a b σ=
      ∑ c∈L,if a≤(assignedSetIndices Q T σ c).card ∧
        b≤(rejectedSetIndices G Q T σ c).card then (1 : ℝ) else 0 :=
    (Finset.sum_boole _ _).symm
  simp_rw [hc,← Finset.sum_sub_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact (threshold_diagonal_sum
    (Finset.card_le_card (rejectedSetIndices_subset_assigned G Q T σ c))
    (Finset.card_le_card (Finset.filter_subset _ _))).symm

end Oberwolfach
