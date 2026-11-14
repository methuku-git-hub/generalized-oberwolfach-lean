module

public import Oberwolfach.IndependentConfigurationSelection
public import Oberwolfach.ConfigurationConflictDeletion

@[expose] public section

/-! A single disjoint family retaining many compatible configurations
for every member of a prescribed finite root family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {C I E : Type*} [Fintype C] [Fintype I] [DecidableEq C] [DecidableEq E]

theorem disjoint_configuration_selection_finite
    (A : C → Finset E) (T : I → Finset C) (P : Finset (C×C))
    (hP : ∀ z∈P,z.1≠z.2)
    (hconflict : ∀ a b,a≠b → ¬Disjoint (A a) (A b) → (a,b)∈P)
    (p u v : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (hu : 0 < u) (hv : 0 < v)
    (hsize : p*Fintype.card C ≤ u) (hpairs : p^2*P.card ≤ v)
    (hfailure : ∑ i : I,2*Real.exp (-p*(T i).card/12)<1/2) :
    ∃ S : Finset C,(S.card:ℝ) ≤ 4*u ∧
      (∀ a∈S,∀ b∈S,a≠b → Disjoint (A a) (A b)) ∧
      ∀ i,p*(T i).card/2-8*v ≤ ((S∩T i).card:ℝ) := by
  let μ := FiniteLaw.pi (fun _ : C => FiniteLaw.retentionCoin p hp hp1)
  let bad : Bool⊕I → (C → Bool) → Prop := fun j σ =>
    match j with
    | .inl false => 4*u ≤ (selectedConfigurationCount Finset.univ σ:ℝ)
    | .inl true => 4*v ≤ (selectedConfigurationPairs P σ:ℝ)
    | .inr i => (selectedConfigurationCount (T i) σ:ℝ)<p*(T i).card/2
  let failure : Bool⊕I → ℝ := fun j =>
    match j with
    | .inl _ => 1/4
    | .inr i => 2*Real.exp (-p*(T i).card/12)
  have hbad (j : Bool⊕I) : μ.probability (bad j) ≤ failure j := by
    rcases j with b | i
    · cases b with
      | false =>
        have hm := finiteLaw_nonnegative_markov μ
          (fun σ => (selectedConfigurationCount Finset.univ σ:ℝ)) (by intro σ;positivity) (4*u) (by positivity)
        have he : μ.expectation (fun σ => (selectedConfigurationCount Finset.univ σ:ℝ)) ≤ u := by
          rw [selectedConfigurationCount_mean]
          simpa using hsize
        exact hm.trans ((div_le_iff₀ (by positivity : 0<4*u)).mpr (by dsimp [failure];linarith))
      | true =>
        have hm := finiteLaw_nonnegative_markov μ
          (fun σ => (selectedConfigurationPairs P σ:ℝ)) (by intro σ;positivity) (4*v) (by positivity)
        have he : μ.expectation (fun σ => (selectedConfigurationPairs P σ:ℝ)) ≤ v := by
          rw [selectedConfigurationPairs_mean p hp hp1 P hP]
          exact hpairs
        exact hm.trans ((div_le_iff₀ (by positivity : 0<4*v)).mpr (by dsimp [failure];linarith))
    · exact selectedConfigurationCount_lower_tail p hp hp1 (T i)
  have hf : ∑ j : Bool⊕I,failure j < 1 := by
    rw [Fintype.sum_sum_type]
    simp only [failure,Fintype.sum_bool]
    linarith
  obtain ⟨σ,_,hσ⟩ := finiteLaw_common_event_exists μ Finset.univ bad failure (fun j _ => hbad j) hf
  let S₀ := Finset.univ.filter (fun c => σ c=true)
  let S := isolatedConfigurations P S₀
  have hS₀ : (S₀.card:ℝ)<4*u := by
    exact lt_of_not_ge (hσ (.inl false) (Finset.mem_univ _))
  have hP₀ : ((selectedConflictPairs P S₀).card:ℝ)<4*v := by
    have he : selectedConflictPairs P S₀=P.filter (fun z => σ z.1=true ∧ σ z.2=true) := by
      ext z;simp [selectedConflictPairs,S₀]
    rw [he]
    exact lt_of_not_ge (hσ (.inl true) (Finset.mem_univ _))
  refine ⟨S,?_,?_,?_⟩
  · have hs : (S.card:ℝ) ≤ S₀.card := by exact_mod_cast Finset.card_le_card (isolatedConfigurations_subset P S₀)
    exact hs.trans hS₀.le
  · exact isolatedConfigurations_disjoint A P S₀ (fun a _ b _ hab h => hconflict a b hab h)
  · intro i
    have hgood : p*(T i).card/2 ≤ (selectedConfigurationCount (T i) σ:ℝ) := by
      exact le_of_not_gt (hσ (.inr i) (Finset.mem_univ _))
    have heq : S₀∩T i=(T i).filter (fun c => σ c=true) := by ext c;simp [S₀,and_comm]
    have hloss : ((S₀∩T i).card:ℝ) ≤ (S∩T i).card+2*((selectedConflictPairs P S₀).card:ℝ) := by
      exact_mod_cast isolatedConfigurations_count_loss P S₀ (T i)
    rw [heq] at hloss
    change ((selectedConfigurationCount (T i) σ):ℝ) ≤ _ at hloss
    linarith

end Oberwolfach
