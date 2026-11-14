module

public import Oberwolfach.ActualSelectedRunFamilyFromPacking
public import Oberwolfach.RawOrdinarySeedPhysicalResources

@[expose] public section
/-! Physical edge-disjointness at one hub separates the rim labels of
ordinary wheels from each other and from marked wheels. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_marked_packing_spokes_distinct
    {V U E L:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    {π:Equiv.Perm V} {b n m:ℕ} {tail head:E→V} {ktail khead:L→V} {H₀ Hₖ:V→U→Prop}
    (C:OrderedOrdinaryWheel (U:=U) π b n) (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hhub:C.2=W.2.val)
    (hdis:Disjoint (ordinaryWheelPhysicalResources C) (markedWheelPhysicalResources W))
    (i:Fin n) (j:Fin (m+1)):C.1.val i≠W.1.val j:=by
  intro he
  have hc:(Sum.inr (C.1.val i,C.2):Finset V⊕(V×U))∈ordinaryWheelPhysicalResources C:=by
    unfold ordinaryWheelPhysicalResources
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hw:(Sum.inr (C.1.val i,C.2):Finset V⊕(V×U))∈markedWheelPhysicalResources W:=by
    apply (markedWheelPhysicalResources_spoke W _ _).mpr
    exact ⟨hhub.symm,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩⟩
  exact Finset.disjoint_left.mp hdis hc hw

theorem ordinary_packing_spokes_distinct
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    {π:Equiv.Perm V} {b n k:ℕ}
    (C:OrderedOrdinaryWheel (U:=U) π b n) (D:OrderedOrdinaryWheel (U:=U) π b k)
    (hhub:C.2=D.2)
    (hdis:Disjoint (ordinaryWheelPhysicalResources C) (ordinaryWheelPhysicalResources D))
    (i:Fin n) (j:Fin k):C.1.val i≠D.1.val j:=by
  intro he
  have hc:(Sum.inr (C.1.val i,C.2):Finset V⊕(V×U))∈ordinaryWheelPhysicalResources C:=by
    unfold ordinaryWheelPhysicalResources
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hd:(Sum.inr (C.1.val i,C.2):Finset V⊕(V×U))∈ordinaryWheelPhysicalResources D:=by
    unfold ordinaryWheelPhysicalResources
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨j,Finset.mem_univ _,by rw [←he,←hhub]⟩
  exact Finset.disjoint_left.mp hdis hc hd
end Oberwolfach
