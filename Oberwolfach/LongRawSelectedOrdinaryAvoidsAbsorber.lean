module

public import Oberwolfach.LongRawSelectedOrdinaryRealization

@[expose] public section
/-! The actual extracted ordinary wheels avoid the fixed absorber in the
retained selected host, using the original two-colour sampling law. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longSelectedAvoidAbsorberFinDecidable (n:ℕ):DecidableEq (Fin n):=
  longRawRealizationsAvoidAbsorberDecidableEqFin1 n
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_raw_selected_ordinary_avoids_fixed_absorber
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ)
    (σ:∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e) (t:ℕ)
    (J:StartRetentionOutcome (rawStartHubSet π d (fun e=>σ (Sum.inr e)) false) t)
    (Reserve:Finset (Finset (Fin n)⊕(Fin n×U))) (X:Finset (Fin n)) (Z:Finset U) (ℓ:Fin K→ℕ):
    let selected:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedMarkedCollapse e (σ e)
    let H:=retainedRawMarkedSpokes π d (fun e=>σ (Sum.inr e)) false t J false false
    let raw:RawMarkedOutcome (Fin n) U Bool Bool:=fun e=>rawExpandedApproximateCollapse e (σ e)
    let state:=longRawHubState P π d raw true true
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    MarkedFixedTerminalAbsorber P π d m selected H Reserve X Z→
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
    ∀a:LongRawSelectedOrdinary π d m ℓ e M,
      Disjoint (ordinaryWheelPhysicalResources (longRawSelectedOrdinaryWheel π d m ℓ e M a).val) Reserve :=by
  intro selected H raw state e R habs M a
  have ha:=long_raw_realizations_avoid_fixed_absorber P π d m σ t J Reserve X Z ℓ habs M a.val a.property.1
  have he:=long_raw_selected_ordinary_realized_resources P π d m ℓ raw true true M a
  convert ha using 1
  convert he.symm using 1 <;> congr 3 <;> exact Subsingleton.elim _ _
end Oberwolfach
