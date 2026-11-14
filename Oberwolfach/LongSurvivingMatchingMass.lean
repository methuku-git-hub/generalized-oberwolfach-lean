module

public import Oberwolfach.RestrictedResourceStateLift
public import Oberwolfach.LongRawHubContext

@[expose] public section
/-! Lifting a matching does not alter its ordinary mass at any hub. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K : ℕ} {U : Type} [Fintype U] [DecidableEq U]

theorem long_surviving_matching_count_preserved
    (π : Equiv.Perm (Fin n)) (d m : ℕ) (ℓ : Fin K → ℕ)
    (S T : Finset (LongRawHubResource n U)) (hST : S ⊆ T)
    (M : Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (· ∈ S)))) (i : Fin K) (w : U) :
    ((M.map (survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST)).filter
      (fun c => c.val.1 = some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2 = w)).card =
    (M.filter (fun c => c.val.1 = some i ∧ longRawSeedHub π d m ℓ c.val.1 c.val.2 = w)).card := by
  rw [Finset.filter_map, Finset.card_map]
  rfl
end Oberwolfach
