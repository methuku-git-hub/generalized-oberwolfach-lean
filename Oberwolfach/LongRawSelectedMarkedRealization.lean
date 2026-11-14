module

public import Oberwolfach.LongRawSelectedOrdinaryRealization

@[expose] public section
/-! Extract marked wheels from the same selected mixed matching, preserving
both candidate identity and its realized physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

abbrev LongRawSelectedMarked {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e)):=
  {c:RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e //
    c∈M ∧ c.val.1=none}

def longRawSelectedMarkedWheel
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    ∀M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e),
      LongRawSelectedMarked π d m ℓ e M→LongRawRealizedWheel P π d m raw g j ℓ none:=by
  intro state e M a
  let lift:=mixedRestrictedPhysicalLift (longRawSeedResources (U:=U) π d m ℓ) e
    (longRawRealizeComponent P π d m raw g j ℓ)
  have hi:(lift a.val).1=none:=a.property.2
  exact hi ▸ (lift a.val).2

theorem long_raw_selected_marked_realized_resources
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
    let B:=fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>longRawRealizedPhysicalResources P π d m raw g j ℓ z.1 z.2
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀a:LongRawSelectedMarked π d m ℓ e M,
      B (lift a.val)=markedWheelPhysicalResources (longRawSelectedMarkedWheel P π d m ℓ raw g j M a):=by
  intro state e R lift B M a
  rcases a with ⟨⟨⟨i,v⟩,hv⟩,ha⟩
  cases i with
  | none =>
    rcases ha with ⟨hm,he⟩
    cases he
    simp [B,lift,R,e,state,longRawHubState,longRawSelectedMarkedWheel,mixedRestrictedPhysicalLift,longRawRealizedPhysicalResources]
    congr 3 <;> exact Subsingleton.elim _ _
  | some i=>simp at ha
end Oberwolfach
