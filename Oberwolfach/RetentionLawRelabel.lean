module

public import Oberwolfach.FixedSubsetRelabel
public import Oberwolfach.UniformStartRetention
public import Oberwolfach.BoundedDifferences
public import Oberwolfach.FiniteLawEquivInverse

@[expose] public section
/-! Exact transport of the conditional independent uniform choices when both
starts and their actual eligible hub sets are relabelled bijectively. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V W U Z : Type} [Fintype V] [Fintype W] [Fintype U] [Fintype Z]
  [DecidableEq V] [DecidableEq W] [DecidableEq U] [DecidableEq Z]

def eligibleHubEquiv (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (w : W) :
    {z // z ∈ B w} ≃ {u // u ∈ A (f w)} where
  toFun z := ⟨g z.val, (h w z.val).mp z.property⟩
  invFun u := ⟨g.symm u.val, (h w (g.symm u.val)).mpr (by simpa using u.property)⟩
  left_inv z := by apply Subtype.ext; exact g.symm_apply_apply z.val
  right_inv u := by apply Subtype.ext; exact g.apply_symm_apply u.val

theorem start_retention_law_relabel
    (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (t : ℕ)
    (ht : ∀ v, t ≤ (A v).card) (ht' : ∀ w, t ≤ (B w).card)
    (E : StartRetentionOutcome A t → Prop) :
    (startRetentionLaw A t ht).probability E =
      (startRetentionLaw B t ht').probability (fun J =>
        E (Equiv.piCongrLeft (fun v => FixedSubset {u // u ∈ A v} t) f
          (fun w => fixedSubsetRelabelEquiv (eligibleHubEquiv f g A B h w) (J w)))) := by
  letI (v : V) : Nonempty (FixedSubset {u // u ∈ A v} t) :=
    fixedSubset_nonempty (by simpa using ht v)
  letI (w : W) : Nonempty (FixedSubset {z // z ∈ B w} t) :=
    fixedSubset_nonempty (by simpa using ht' w)
  let μ : ∀ v, FiniteLaw (FixedSubset {u // u ∈ A v} t) :=
    fun v => FiniteLaw.uniform _
  let ν : ∀ w, FiniteLaw (FixedSubset {z // z ∈ B w} t) :=
    fun w => FiniteLaw.uniform _
  let φ := fun w => fixedSubsetRelabelEquiv (t := t) (eligibleHubEquiv f g A B h w)
  have hm : ∀ w, (ν w).map (φ w) = μ (f w) := by
    intro w
    exact fixed_subset_relabel_uniform (eligibleHubEquiv f g A B h w)
  change (FiniteLaw.pi μ).probability E = (FiniteLaw.pi ν).probability _
  rw [finiteLaw_pi_reindex_probability f μ E]
  conv_lhs => rw [show (fun w => μ (f w)) = (fun w => (ν w).map (φ w)) from funext (fun w => (hm w).symm)]
  rw [← finiteLaw_pi_map ν (fun w => φ w), finiteLaw_map_probability]
def startRetentionRelabelEquiv
    (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (t : ℕ) :
    StartRetentionOutcome B t ≃ StartRetentionOutcome A t :=
  (Equiv.piCongrRight (fun w => fixedSubsetRelabelEquiv
    (eligibleHubEquiv f g A B h w))).trans
    (Equiv.piCongrLeft (fun v => FixedSubset {u // u ∈ A v} t) f)

theorem start_retention_law_relabel_map
    (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (t : ℕ)
    (ht : ∀ v, t ≤ (A v).card) (ht' : ∀ w, t ≤ (B w).card) :
    (startRetentionLaw B t ht').map (startRetentionRelabelEquiv f g A B h t) =
      startRetentionLaw A t ht := by
  apply finiteLaw_ext
  intro J
  have hh := start_retention_law_relabel f g A B h t ht ht' (fun J' => J' = J)
  change (startRetentionLaw A t ht).probability (fun J' => J' = J) =
    (startRetentionLaw B t ht').probability (fun J' => startRetentionRelabelEquiv f g A B h t J' = J) at hh
  have hm := finiteLaw_map_probability (startRetentionLaw B t ht') (startRetentionRelabelEquiv f g A B h t) (fun J' => J' = J)
  have hh' := hm.trans hh.symm
  have hp (L : FiniteLaw (StartRetentionOutcome A t)) :
      L.probability (fun J' => J' = J) = L.mass J := by
    unfold FiniteLaw.probability
    rw [Finset.sum_eq_single J]
    · simp
    · intro x hx hne
      simp [hne]
    · simp
  rw [hp, hp] at hh'
  exact hh' 
theorem start_retention_law_inverse_cast
    (f : W ≃ V) (g : Z ≃ U) (A : V → Finset U) (B : W → Finset Z)
    (h : ∀ w z, z ∈ B w ↔ g z ∈ A (f w)) (t u : ℕ) (he : u = t)
    (ht : ∀ v, t ≤ (A v).card) (hu : ∀ w, u ≤ (B w).card) :
    (startRetentionLaw A t ht).map (fun J =>
      he.symm ▸ (startRetentionRelabelEquiv f g A B h t).symm J) =
    startRetentionLaw B u hu := by
  cases he
  exact finiteLaw_map_equiv_inverse _ _ (startRetentionRelabelEquiv f g A B h t)
    (start_retention_law_relabel_map f g A B h t ht hu)
end Oberwolfach
