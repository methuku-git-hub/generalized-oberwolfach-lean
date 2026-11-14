module

public import Oberwolfach.MarkedSupportedResourceBounds
public import Oberwolfach.MarkedRemainderActiveSets

@[expose] public section

/-! Count all possible finite remainders on a fixed terminal pair. The
bound depends only on the terminal vertex bound, not on the ambient order.
Ordinary and twisted rims are counted through their injective physical map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_remainder_rows_mono (tail head:E→V) (ktail khead:K→V)
    {A A':Finset (E⊕K)} {S S':Finset (V×U)} (hA:A⊆A') (hS:S⊆S'):
    markedRemainderRows tail head ktail khead A S⊆markedRemainderRows tail head ktail khead A' S':=
  Finset.union_subset_union (Finset.union_subset_union (Finset.image_subset_image hA)
    (Finset.image_subset_image hA)) (Finset.image_subset_image hS)

theorem marked_remainder_resources_old (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (A:Finset (E⊕K)) (S:Finset (V×U)) (X:Finset V) (Z:Finset U)
    (hr:markedRemainderRows tail head ktail khead A S⊆X) (hu:markedRemainderHubs S⊆Z):
    ∀ e∈A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr,
      MarkedOldResource tail head ktail khead π X Z e:=by
  intro e he
  rcases Finset.mem_union.mp he with he|he
  · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp he
    refine ⟨a,rfl,hr ?_,hr ?_⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,ha,rfl⟩))
  · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp he
    exact ⟨hr (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,hz,rfl⟩)),hu (Finset.mem_image.mpr ⟨z,hz,rfl⟩)⟩

theorem marked_remainder_resource_card (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A:Finset (E⊕K)) (S:Finset (V×U)):
    (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr).card=A.card+S.card:=by
  have hd:Disjoint (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a)))
      (S.image (Sum.inr:V×U→Finset V⊕(V×U))):=by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨a,_,rfl⟩:=Finset.mem_image.mp he
    obtain ⟨z,_,he⟩:=Finset.mem_image.mp hf
    exact Sum.inr_ne_inl he
  rw [Finset.card_union_of_disjoint hd]
  congr 1
  · exact Finset.card_image_of_injective A (fun a b he=>hp (Sum.inl.inj he))
  · exact Finset.card_image_of_injective S Sum.inr_injective

theorem marked_terminal_resource_count (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (A:Finset (E⊕K)) (S:Finset (V×U)) (X:Finset V) (Z:Finset U) (s:ℕ)
    (hr:markedRemainderRows tail head ktail khead A S⊆X) (hu:markedRemainderHubs S⊆Z)
    (hs:X.card+Z.card≤s):A.card+S.card≤2*s^2:=by
  let C:MarkedSupportedEdgeSet tail head ktail khead π U:=
    ⟨X,Z,A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr,
      marked_remainder_resources_old tail head ktail khead π A S X Z hr hu⟩
  have hbound:=marked_supported_edges_card C X.card Z.card le_rfl le_rfl
  have hcount:C.edges.card=A.card+S.card:=marked_remainder_resource_card tail head ktail khead π hp A S
  rw [hcount] at hbound
  have hXs:X.card≤s:=by omega
  have hprod:=Nat.mul_le_mul_left X.card hs
  have hsq:=Nat.mul_self_le_mul_self hXs
  have hXsprod:=Nat.mul_le_mul_right s hXs
  nlinarith only [hbound,hprod,hsq,hXsprod]

end Oberwolfach
