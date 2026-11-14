module

public import Oberwolfach.MarkedHubRowProtectedBounds
public import Oberwolfach.MarkedProtectedResourceRestoration

@[expose] public section

/-! The deep-stage packing avoids every edge incident with the remaining
inner rows and hubs, a stronger assertion than avoiding induced inner edges. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b m n h:ℕ} {H₀ HK:V→U→Prop}

theorem marked_wheel_avoids_star
    (T:Finset V) (Z:Finset U) (hT:∀ x,π x∈T↔x∈T)
    (W:MarkedWheel tail head ktail khead m π b H₀ HK)
    (hrows:∀ x∈markedWheelRows W,x∉T) (hhub:W.2.val∉Z):
    (markedWheelPhysicalResources W).filter (markedStarResource T Z)=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr,hs⟩:=Finset.mem_filter.mp hr
  cases r with
  | inl e=>
    obtain ⟨x,hx,hxt⟩:=hs
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp hr)
    simp only [Function.comp_apply] at hi
    have hp:=markedCycle_physical_pair tail head ktail khead π b W.1 i
    have hpair:x∈({W.1.val i,twistedTupleHead π W.1.val i}:Finset V):=by
      rw [←hp,hi]
      exact hx
    rcases Finset.mem_insert.mp hpair with hi'|hi'
    · exact hrows _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩) (hi' ▸ hxt)
    · have he:x=twistedTupleHead π W.1.val i:=Finset.mem_singleton.mp hi'
      subst x
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j,rfl⟩|rfl
      · exact hrows _ (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩)
          (by simpa only [twistedTupleHead,Fin.snoc_castSucc] using hxt)
      · apply hrows _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)
        apply (hT _).mp
        simpa only [twistedTupleHead,Fin.snoc_last] using hxt
  | inr z=>
    obtain ⟨hu,hx⟩:=(markedWheelPhysicalResources_spoke W _ _).mp hr
    rcases hs with ht|hz
    · exact hrows _ hx ht
    · exact hhub (hu ▸ hz)

theorem marked_hub_row_supported_avoids_star
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (u:Fin h→U) (v:Fin n→V) (F T:Finset V) (Z:Finset U) (Y:Fin n→Finset U)
    (hsupport:∀ W∈M,
      (W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
      ∃ i,W.2.val∈Y i∧markedWheelRows W⊆insert (v i) F)
    (hFT:Disjoint F T) (hv:∀ i,v i∉T) (hT:∀ x,π x∈T↔x∈T)
    (hu:Disjoint (Finset.univ.image u) Z) (hY:∀ i,Disjoint (Y i) Z):
    (M.biUnion markedWheelPhysicalResources).filter (markedStarResource T Z)=∅:=by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro r hr
  obtain ⟨hr,hs⟩:=Finset.mem_filter.mp hr
  obtain ⟨W,hW,hr⟩:=Finset.mem_biUnion.mp hr
  have he:(markedWheelPhysicalResources W).filter (markedStarResource T Z)=∅:=by
    rcases hsupport W hW with ⟨hw,hr⟩|⟨i,hw,hr⟩
    · exact marked_wheel_avoids_star T Z hT W
        (fun x hx=>Finset.disjoint_left.mp hFT (hr hx)) (Finset.disjoint_left.mp hu hw)
    · apply marked_wheel_avoids_star T Z hT W
      · intro x hx
        rcases Finset.mem_insert.mp (hr hx) with hx|hx
        · exact hx ▸ hv i
        · exact Finset.disjoint_left.mp hFT hx
      · exact Finset.disjoint_left.mp (hY i) hw
  have hh:=Finset.mem_filter.mpr ⟨hr,hs⟩
  rw [he] at hh
  exact Finset.notMem_empty r hh


theorem marked_hub_row_avoids_remaining_inner_star
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (u:Fin h→U) (v:Fin n→V) (F I T:Finset V) (J Z:Finset U) (Y:Fin n→Finset U)
    (hsupport:∀ W∈M,
      (W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
      ∃ i,W.2.val∈Y i∧markedWheelRows W⊆insert (v i) F)
    (hFI:Disjoint F I) (hv:∀ i,v i∈T)
    (hI:∀ x,π x∈I↔x∈I) (hT:∀ x,π x∈T↔x∈T)
    (hu:∀ i,u i∈Z) (hY:∀ i,Disjoint (Y i) J):
    (M.biUnion markedWheelPhysicalResources).filter (markedStarResource (I\T) (J\Z))=∅:=by
  apply marked_hub_row_supported_avoids_star M u v F (I\T) (J\Z) Y hsupport
  · exact hFI.mono_right Finset.sdiff_subset
  · intro i hi
    exact (Finset.mem_sdiff.mp hi).2 (hv i)
  · intro x;simp only [Finset.mem_sdiff,hI,hT]
  · apply Finset.disjoint_left.mpr
    intro z hz hz'
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hz
    exact (Finset.mem_sdiff.mp hz').2 (hu i)
  · intro i;exact (hY i).mono_right Finset.sdiff_subset

end Oberwolfach
