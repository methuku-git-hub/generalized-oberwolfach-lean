module

public import Oberwolfach.LongRawSelectedOrdinaryMatching
public import Oberwolfach.AssignedRestrictedOrdinaryWheelMaps

@[expose] public section
/-! Given the component assignment, the actual selected ordinary mixed
candidates provide edge-respecting maps with disjoint images at each hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U X:Type} [Fintype U] [DecidableEq U] [Fintype X] [DecidableEq X]

theorem long_raw_selected_ordinary_component_maps
    (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
    (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ) (e:X↪LongRawHubResource n U)
    (M:Finset (RestrictedResource (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e))
    (hmatch:∀c∈M,∀c'∈M,c≠c'→Disjoint
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e c)
      (restrictedResourceSet (mixedCandidateResources (longRawSeedResources (U:=U) π d m ℓ)) e c')):
    let A:=LongRawSelectedOrdinary π d m ℓ e M
    let Q:=longRawSelectedOrdinaryWheel π d m ℓ e M
    let r:=fun a:A=>ℓ (longRawSelectedOrdinaryPayload π d m ℓ e M a).1
    ∀(C:∀a:A,(F (Q a).val.2).ConnectedComponent),
      (∀a,Fintype.card (C a)=r a) →
    ∃ f:∀a:A,(C a)↪Fin n,
      (∀a x,∃i:Fin (r a),f a x=(Q a).val.1.val i) ∧
      (∀a,∀i:Fin (r a),∃x:C a,f a x=(Q a).val.1.val i) ∧
      (∀a x y,(C a).toSimpleGraph.Adj x y→
        ∃i:Fin (r a),(f a x=(Q a).val.1.val i ∧ f a y=(Q a).val.1.val (cycleNext i)) ∨
          (f a y=(Q a).val.1.val i ∧ f a x=(Q a).val.1.val (cycleNext i))) ∧
      (∀a x,Sum.inr (f a x,(Q a).val.2)∈orderedOrdinaryResources (Q a).val) ∧
      (∀a a',a≠a'→(Q a).val.2=(Q a').val.2→
        Disjoint (Finset.univ.image (f a)) (Finset.univ.image (f a'))) :=by
  intro A Q r C hsize
  apply assigned_restricted_ordinary_wheel_maps F hF π (3*d) r e Q C hsize
  intro a a' hne _
  exact long_raw_selected_ordinary_restricted_matching π d m ℓ e M hmatch a a' hne
end Oberwolfach
