module

public import Oberwolfach.LongRawPhysicalHubRims
public import Oberwolfach.LongRawSelectedOrdinaryRealization

@[expose] public section
/-! Every rim edge of every selected marked or ordinary wheel belongs to
the original matching's physical rim set at that wheel's hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance longRawWheelRimDecEqFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem long_raw_selected_wheel_rims_covered
    {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (P:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)) (d m:ℕ) (ℓ:Fin K→ℕ)
    (raw:RawMarkedOutcome (Fin n) U Bool Bool) (g j:Bool):
    let state:=longRawHubState P π d raw g j
    let e:{z // z∈bernoulliVertexSet state}↪_:=Function.Embedding.subtype _
    let R:=longRawSeedResources (U:=U) π d m ℓ
    ∀M:Finset (RestrictedResource (mixedCandidateResources R) e),
      (∀a:LongRawSelectedMarked π d m ℓ e M,∀x,
        x∈markedCyclePhysicalEdges _ _ _ _ m π (3*d) (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).1→
        x∈longRawPhysicalHubRims P π d m ℓ raw g j M (longRawSelectedMarkedWheel P π d m ℓ raw g j M a).2.val) ∧
      (∀a:LongRawSelectedOrdinary π d m ℓ e M,∀k,
        {((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val k),
         ((longRawSelectedOrdinaryWheel π d m ℓ e M a).val.1.val (cycleNext k))}∈
          longRawPhysicalHubRims P π d m ℓ raw g j M (longRawSelectedOrdinaryWheel π d m ℓ e M a).val.2):=by
  intro state e R M
  constructor
  · intro a x hx
    have hx':Sum.inl x∈markedWheelPhysicalResources (longRawSelectedMarkedWheel P π d m ℓ raw g j M a):=
      (markedWheelPhysicalResources_rim _ x).mpr hx
    have hEq:longRawWheelRimDecEqFin n=instDecidableEqFin n:=Subsingleton.elim _ _
    rw [hEq] at hx'
    have heq:=long_raw_selected_marked_realized_resources P π d m ℓ raw g j M a
    have hm:Sum.inl x∈(fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>longRawRealizedPhysicalResources P π d m raw g j ℓ z.1 z.2)
        (mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ) a.val):=by rw [heq];exact hx'
    have hh:=long_raw_realized_rim_in_its_hub P π d m ℓ raw g j M a.val a.property.1 x hm
    rw [long_raw_selected_marked_hub P π d m ℓ raw g j M a]
    exact hh
  · intro a k
    let W:=(longRawSelectedOrdinaryWheel π d m ℓ e M a).val
    let x:Finset (Fin n):={W.1.val k,W.1.val (cycleNext k)}
    have hx:Sum.inl x∈ordinaryWheelPhysicalResources W:=by
      unfold ordinaryWheelPhysicalResources
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩)
    have heq:=long_raw_selected_ordinary_realized_resources P π d m ℓ raw g j M a
    have hm:Sum.inl x∈(fun z:Σi,LongRawRealizedWheel P π d m raw g j ℓ i=>longRawRealizedPhysicalResources P π d m raw g j ℓ z.1 z.2)
        (mixedRestrictedPhysicalLift R e (longRawRealizeComponent P π d m raw g j ℓ) a.val):=by rw [heq];exact hx
    have hh:=long_raw_realized_rim_in_its_hub P π d m ℓ raw g j M a.val a.property.1 x hm
    rw [long_raw_selected_ordinary_hub π d m ℓ e M a]
    exact hh
end Oberwolfach
