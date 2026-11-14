module

public import Oberwolfach.SubsetComplement
public import Oberwolfach.SubsetInclusion
public import Oberwolfach.CommonEvents

@[expose] public section

/-! Joint deletion bounds retain the uniform fixed-size law. A binomial
union bound requires bounds on prescribed subsets, not independence of
individual membership events. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem finiteLaw_set_count_tail {Ω V : Type*} [Fintype Ω] [DecidableEq V]
    (μ : FiniteLaw Ω) (X : Ω→Finset V) (T : Finset V) (k : ℕ) (p : ℝ)
    (hjoint : ∀ A∈T.powersetCard k,μ.probability (fun ω=>A⊆X ω)≤p^k) :
    μ.probability (fun ω=>k≤(T∩X ω).card)≤(T.card.choose k:ℝ)*p^k := by
  have hsub : ∀ ω,k≤(T∩X ω).card → ∃ A∈T.powersetCard k,A⊆X ω := by
    intro ω h
    obtain ⟨A,hA,hcard⟩ := Finset.exists_subset_card_eq h
    exact ⟨A,Finset.mem_powersetCard.mpr ⟨hA.trans Finset.inter_subset_left,hcard⟩,
      hA.trans Finset.inter_subset_right⟩
  have hu := finiteLaw_union_bound μ (T.powersetCard k) (fun A ω=>A⊆X ω)
  calc
    _ ≤ μ.probability (fun ω=>∃ A∈T.powersetCard k,A⊆X ω) := finiteLaw_probability_mono μ _ _ hsub
    _ ≤ ∑ A∈T.powersetCard k,μ.probability (fun ω=>A⊆X ω) := hu
    _ ≤ ∑ _A∈T.powersetCard k,p^k := Finset.sum_le_sum hjoint
    _ = _ := by simp

theorem fixedSubset_joint_exclusion_le {V : Type*} [Fintype V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r≤Fintype.card V) (T : Finset V) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S=>T⊆S.valᶜ)≤
      ((Fintype.card V-r:ℕ):ℝ)^T.card/(Fintype.card V:ℝ)^T.card := by
  letI := fixedSubset_nonempty (V:=V) (Nat.sub_le (Fintype.card V) r)
  have he := finiteLaw_uniform_map_equiv (fixedSubsetComplEquiv (V:=V) hr)
  have hp := fixedSubset_joint_inclusion_le (V:=V) (Nat.sub_le (Fintype.card V) r) T
  rw [← he,finiteLaw_map_probability] at hp
  simpa only [fixedSubsetComplEquiv,Equiv.coe_fn_mk,div_pow] using hp

theorem fixedSubset_deleted_intersection_tail {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    [Nonempty (FixedSubset V r)] (hr : r≤Fintype.card V) (T : Finset V) (k : ℕ) :
    (FiniteLaw.uniform (FixedSubset V r)).probability (fun S=>k≤(T∩S.valᶜ).card)≤
      (T.card.choose k:ℝ)*(((Fintype.card V-r:ℕ):ℝ)/Fintype.card V)^k := by
  apply finiteLaw_set_count_tail (FiniteLaw.uniform (FixedSubset V r)) (fun S=>S.valᶜ) T k _
  intro A hA
  have hc := (Finset.mem_powersetCard.mp hA).2
  have hh := fixedSubset_joint_exclusion_le hr A
  simp only [Finset.subset_iff,Finset.mem_compl] at hh ⊢
  simpa only [hc,div_pow] using hh

end Oberwolfach
