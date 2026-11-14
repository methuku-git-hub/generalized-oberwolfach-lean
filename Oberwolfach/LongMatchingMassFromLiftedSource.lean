module

public import Oberwolfach.LongSurvivingMatchingMass

@[expose] public section
/-! Transfer a source-mass estimate to the matching before resource lifting. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K : ℕ} {U : Type} [Fintype U] [DecidableEq U]

theorem long_matching_mass_from_lifted_source
    (π : Equiv.Perm (Fin n)) (d m : ℕ) (ℓ : Fin K → ℕ)
    (S T : Finset (LongRawHubResource n U)) (hST : S ⊆ T)
    (M : Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (· ∈ S)))) (w : U)
    (sourceCard : ℕ) (target err : ℝ)
    (hcount : sourceCard = ∑ i : Fin K,
      ((M.map (survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST)).filter
        (fun c => c.val.1 = some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2 = w)).card * ℓ i)
    (hsource : |(sourceCard : ℝ) - target| ≤ err) :
    |((∑ i : Fin K, (M.filter (fun c => c.val.1 = some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2 = w)).card * ℓ i : ℕ) : ℝ) - target| ≤ err := by
  have hsum : sourceCard = ∑ i : Fin K, (M.filter (fun c => c.val.1 = some i ∧
      longRawSeedHub π d m ℓ c.val.1 c.val.2 = w)).card * ℓ i := by
    rw [hcount]
    apply Finset.sum_congr rfl
    intro i hi
    rw [long_surviving_matching_count_preserved π d m ℓ S T hST M i w]
  simpa only [← hsum] using hsource
end Oberwolfach
