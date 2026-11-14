module

public import Oberwolfach.SelectedSubtypeMapEquiv
public import Oberwolfach.LongRawSelectedOrdinary
public import Oberwolfach.RestrictedResourceStateLift

@[expose] public section
/-! Ordinary selected candidates are unchanged by lifting surviving resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K : ℕ} {U : Type} [Fintype U] [DecidableEq U]

def longSelectedOrdinarySurvivalEquiv
    (π : Equiv.Perm (Fin n)) (d m : ℕ) (ℓ : Fin K → ℕ)
    (S T : Finset (LongRawHubResource n U)) (hST : S ⊆ T)
    (M : Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (· ∈ S)))) :
    LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (· ∈ S)) M ≃
      LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (· ∈ T))
        (M.map (survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST)) := by
  apply selectedSubtypeMapEquiv
  intro a
  rfl

theorem longSelectedOrdinarySurvivalEquiv_index
    (π : Equiv.Perm (Fin n)) (d m : ℕ) (ℓ : Fin K → ℕ)
    (S T : Finset (LongRawHubResource n U)) (hST : S ⊆ T)
    (M : Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (· ∈ S))))
    (a : LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (· ∈ S)) M) :
    (longRawSelectedOrdinaryPayload π d m ℓ (Function.Embedding.subtype (· ∈ S)) M a).1 =
    (longRawSelectedOrdinaryPayload π d m ℓ (Function.Embedding.subtype (· ∈ T))
      (M.map (survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST))
      (longSelectedOrdinarySurvivalEquiv π d m ℓ S T hST M a)).1 := by
  rcases a with ⟨⟨⟨i,v⟩,hv⟩,hM,hi⟩
  cases i with
  | none => simp at hi
  | some i => rfl

theorem longSelectedOrdinarySurvivalEquiv_hub
    (π : Equiv.Perm (Fin n)) (d m : ℕ) (ℓ : Fin K → ℕ)
    (S T : Finset (LongRawHubResource n U)) (hST : S ⊆ T)
    (M : Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ))
      (Function.Embedding.subtype (· ∈ S))))
    (a : LongRawSelectedOrdinary π d m ℓ (Function.Embedding.subtype (· ∈ S)) M) :
    (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (· ∈ S)) M a).val.2 =
    (longRawSelectedOrdinaryWheel π d m ℓ (Function.Embedding.subtype (· ∈ T))
      (M.map (survivingCandidateEmbedding (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) S T hST))
      (longSelectedOrdinarySurvivalEquiv π d m ℓ S T hST M a)).val.2 := by
  rcases a with ⟨⟨⟨i,v⟩,hv⟩,hM,hi⟩
  cases i with
  | none => simp at hi
  | some i => rfl
end Oberwolfach
