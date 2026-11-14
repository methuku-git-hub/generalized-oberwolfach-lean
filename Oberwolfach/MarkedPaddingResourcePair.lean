module

public import Oberwolfach.MarkedPaddingPairConstruction
public import Oberwolfach.MarkedInitialDiagramOldResources
public import Oberwolfach.ResourceFamilyIndicators
public import Oberwolfach.ResourceTransformerPadding

@[expose] public section

/-! Both actual padding families are decomposable, disjoint from one
another, and disjoint from the two original root graphs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K I:Type} [Fintype I] [DecidableEq V] [DecidableEq U] [DecidableEq I]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

def pairedPaddingResources (C:Bool×I→MarkedWheel tail head ktail khead m π b H₀ HK) (j:Bool):
    Finset (Finset V⊕(V×U)):=Finset.univ.biUnion (fun i:I=>markedWheelPhysicalResources (C (j,i)))

theorem marked_padding_resource_pair (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:Bool×I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (v:Bool×I→V) (p:Bool×I→(Fin m↪V)) (Z:Finset V) (B:Finset U)
    (hC:∀ i k,(C i).1.val k=Fin.cons (α:=fun _=>V) (v i) (p i) k)
    (hav:∀ i k,p i k∉Z) (hh:∀ i,(C i).2.val∉B)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))
    (L L':Finset (Finset V⊕(V×U)))
    (hL:∀ e∈L∪L',MarkedOldResource tail head ktail khead π Z B e):
    (∀ j:Bool,HasResourceDecomposition (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) (pairedPaddingResources C j))∧
    Disjoint (pairedPaddingResources C false) (pairedPaddingResources C true)∧
    Disjoint (pairedPaddingResources C false∪pairedPaddingResources C true) (L∪L'):=by
  have hi:∀ i,Disjoint (markedWheelPhysicalResources (C i)) (L∪L'):=by
    intro i
    apply marked_padding_avoids_old_resources hm hp (C i) (v i) (p i) Z B (hC i) (hav i) (hh i) (L∪L')
    intro e he
    cases e with
    | inl e=>exact hL _ he
    | inr vu=>exact (hL _ he).2
  refine ⟨?_,?_,?_⟩
  · intro j
    exact resource_indexed_family_decomposition markedWheelPhysicalResources (fun i=>C (j,i))
      (fun i k hik=>hpack (j,i) (j,k) (fun he=>hik (congrArg Prod.snd he)))
  · apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he
    obtain ⟨i',_,he'⟩:=Finset.mem_biUnion.mp he'
    exact Finset.disjoint_left.mp (hpack (false,i) (true,i') (by simp)) he he'
  · apply Finset.disjoint_left.mpr
    intro e he he'
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he;exact Finset.disjoint_left.mp (hi (false,i)) he he'
    · obtain ⟨i,_,he⟩:=Finset.mem_biUnion.mp he;exact Finset.disjoint_left.mp (hi (true,i)) he he'

theorem marked_transformer_unpad (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C:Bool×I→MarkedWheel tail head ktail khead m π b H₀ HK)
    (v:Bool×I→V) (p:Bool×I→(Fin m↪V)) (Z:Finset V) (B:Finset U)
    (hC:∀ i k,(C i).1.val k=Fin.cons (α:=fun _=>V) (v i) (p i) k)
    (hav:∀ i k,p i k∉Z) (hh:∀ i,(C i).2.val∉B)
    (hpack:∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))
    (L L' T:Finset (Finset V⊕(V×U)))
    (hL:∀ e∈L∪L',MarkedOldResource tail head ktail khead π Z B e)
    (hT:IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK))
      (L∪pairedPaddingResources C false) (L'∪pairedPaddingResources C true) T):
    IsResourceTransformer (markedWheelPhysicalResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
      (m:=m) (π:=π) (b:=b) (H₀:=H₀) (Hₖ:=HK)) L L'
      (T∪pairedPaddingResources C false∪pairedPaddingResources C true):=by
  obtain ⟨hd,hpP,hPL⟩:=marked_padding_resource_pair hm hp C v p Z B hC hav hh hpack L L' hL
  exact resource_transformer_remove_padding markedWheelPhysicalResources L L' _ _ T hT (hd false) (hd true)
    (hPL.mono Finset.subset_union_left Finset.subset_union_left).symm
    (hPL.mono Finset.subset_union_right Finset.subset_union_left).symm
    (hPL.mono Finset.subset_union_left Finset.subset_union_right).symm
    (hPL.mono Finset.subset_union_right Finset.subset_union_right).symm hpP

end Oberwolfach
