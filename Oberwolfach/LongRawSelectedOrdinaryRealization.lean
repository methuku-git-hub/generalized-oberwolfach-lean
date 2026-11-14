module

public import Oberwolfach.LongRawSelectedOrdinaryMatching
public import Oberwolfach.LongRawRealizationsAvoidAbsorber

@[expose] public section
/-! The physical realization of a selected ordinary mixed candidate is
exactly the extracted ordinary wheel, including all its resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_selected_ordinary_realized_resources
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    let lift:=mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ)
    let B:=fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>
      longRawRealizedPhysicalResources P π d m raw g j ℓ z.1 z.2
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀a:LongRawSelectedOrdinary π d m ℓ e M,
      B (lift a.val)=ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val :=by
  intro state e R lift B M a
  rcases a with ⟨⟨⟨i,v⟩,hv⟩,ha⟩
  cases i with
  | none => simp at ha
  | some i => rfl
end Oberwolfach
