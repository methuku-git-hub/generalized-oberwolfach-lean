module

public import Oberwolfach.LongRawSelectedMarkedRealization

@[expose] public section
/-! The marked wheel extracted from the original matching keeps the
candidate's original hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_raw_selected_marked_hub
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
    ∀a:LongRawSelectedMarked π d m ℓ e M,
      (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).2.val=
        longRawSeedHub π d m ℓ a.val.val.1 a.val.val.2:=by
  intro state e M a
  have h:=long_raw_matching_realization_preserves_hub P π d m raw g j ℓ a.val
  rcases a with ⟨⟨⟨i,v⟩,hv⟩,ha⟩
  cases i with
  | none =>
    rcases ha with ⟨hm,he⟩
    cases he
    simp [state,e,longRawHubState,longRawSelectedMarkedWheel,mixedRestrictedPhysicalLift,longRawRealizedHub] at h ⊢
    convert h using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
  | some i=>simp at ha
end Oberwolfach
