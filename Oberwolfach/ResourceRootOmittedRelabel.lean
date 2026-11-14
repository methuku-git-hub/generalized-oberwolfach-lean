module

public import Oberwolfach.ResourceRootOmittedLoads

@[expose] public section
/-! Exact transport of a fixed root-omitted load under bijections of the
occurrences and resources. The root is not required to be kept. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I J A B : Type} [Fintype I] [Fintype J] [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem resource_root_omitted_load_relabel
    (ei : I ≃ J) (ea : A ≃ B) (R : I → Finset A) (S : J → Finset B)
    (hR : ∀ i, S (ei i) = (R i).image ea) (w : J → ℝ)
    (keep : A → Prop) (keep' : B → Prop) (hk : ∀ a, keep a ↔ keep' (ea a)) (root : A) :
    resourceRootOmittedLoad R (fun i => w (ei i)) keep root =
      resourceRootOmittedLoad S w keep' (ea root) := by
  unfold resourceRootOmittedLoad
  rw [← ei.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hroot : root ∈ R i ↔ ea root ∈ S (ei i) := by
    rw [hR,Finset.mem_image]
    constructor
    · intro h
      exact ⟨root,h,rfl⟩
    · rintro ⟨a,ha,he⟩
      exact ea.injective he ▸ ha
  have hkeep : (∀ a∈R i, a≠root → keep a) ↔
      (∀ b∈S (ei i), b≠ea root → keep' b) := by
    constructor
    · intro hh b hb hne
      rw [hR,Finset.mem_image] at hb
      obtain ⟨a,ha,rfl⟩ := hb
      apply (hk a).mp
      exact hh a ha (fun he => hne (congrArg ea he))
    · intro hh a ha hne
      apply (hk a).mpr
      apply hh (ea a)
      · rw [hR,Finset.mem_image]
        exact ⟨a,ha,rfl⟩
      · intro he
        exact hne (ea.injective he)
  exact if_congr (and_congr hroot hkeep) rfl rfl
theorem resource_omitted_pair_weight_relabel
    (ei : I ≃ J) (ea : A ≃ B) (R : I → Finset A) (S : J → Finset B)
    (hR : ∀ i, S (ei i) = (R i).image ea) (w : J → ℝ) (root other : A) :
    resourceOmittedPairWeight R (fun i => w (ei i)) root other =
      resourceOmittedPairWeight S w (ea root) (ea other) := by
  unfold resourceOmittedPairWeight
  rw [← ei.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  have hm (a : A) : a ∈ R i ↔ ea a ∈ S (ei i) := by
    rw [hR, Finset.mem_image]
    constructor
    · intro h
      exact ⟨a,h,rfl⟩
    · rintro ⟨b,hb,he⟩
      exact ea.injective he ▸ hb
  have hn : other ≠ root ↔ ea other ≠ ea root := by
    constructor
    · intro h he; exact h (ea.injective he)
    · intro h he; exact h (congrArg ea he)
  exact if_congr (and_congr (hm root) (and_congr (hm other) hn)) rfl rfl
end Oberwolfach
