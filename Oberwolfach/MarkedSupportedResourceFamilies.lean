module

public import Oberwolfach.MarkedResourceExclusions
public import Oberwolfach.PermutationClose

@[expose] public section

/-! Explicit auxiliary row and hub supports for jointly selected resources.
The physical resources, rather than their vertex labels, must be disjoint. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}

structure MarkedSupportedEdgeSet (tail head:E→V) (ktail khead:K→V) (π:Equiv.Perm V) (U:Type) [DecidableEq U] where
  rows:Finset V
  hubs:Finset U
  edges:Finset (Finset V⊕(V×U))
  supported:∀ e∈edges,MarkedOldResource tail head ktail khead π rows hubs e

def emptyMarkedSupportedEdgeSet:MarkedSupportedEdgeSet tail head ktail khead π U:=
  ⟨∅,∅,∅,by simp⟩

theorem marked_supported_sets_disjoint_of_free
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (C D:MarkedSupportedEdgeSet tail head ktail khead π U) (Z:Finset V) (B:Finset U)
    (hrows:Disjoint (C.rows\Z) (D.rows\Z)) (hhubs:Disjoint (C.hubs\B) (D.hubs\B))
    (hC:∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π Z B e):Disjoint C.edges D.edges:=by
  have hr:∀ v∈C.rows,v∈D.rows→v∈Z:=by
    intro v hc hd;by_contra hz
    exact Finset.disjoint_left.mp hrows (Finset.mem_sdiff.mpr ⟨hc,hz⟩) (Finset.mem_sdiff.mpr ⟨hd,hz⟩)
  have hh:∀ u∈C.hubs,u∈D.hubs→u∈B:=by
    intro u hc hd;by_contra hb
    exact Finset.disjoint_left.mp hhubs (Finset.mem_sdiff.mpr ⟨hc,hb⟩) (Finset.mem_sdiff.mpr ⟨hd,hb⟩)
  apply Finset.disjoint_left.mpr
  intro e hc hd
  apply hC e hc
  cases e with
  | inl e=>
    obtain ⟨a,ha,hat,hah⟩:=C.supported _ hc
    obtain ⟨a',ha',hat',hah'⟩:=D.supported _ hd
    have he:a=a':=hp (ha.trans ha'.symm)
    subst a'
    exact ⟨a,ha,hr _ hat hat',hr _ hah hah'⟩
  | inr vu=>exact ⟨hr _ (C.supported _ hc).1 (D.supported _ hd).1,hh _ (C.supported _ hc).2 (D.supported _ hd).2⟩

variable [Fintype V]

def markedCloseSet (π:Equiv.Perm V) (b:ℕ) (Z:Finset V):Finset V:=
  Z.biUnion (fun z=>Finset.univ.filter (fun v=>PermutationClose π b z v))

theorem markedCloseSet_card (π:Equiv.Perm V) (b:ℕ) (Z:Finset V):
    (markedCloseSet π b Z).card≤Z.card*(2*b+1):=by
  apply Finset.card_biUnion_le_card_mul
  intro z hz
  rw [←Fintype.card_subtype]
  exact permutationClose_neighbour_card π b z

theorem mem_markedCloseSet (π:Equiv.Perm V) (b:ℕ) (Z:Finset V) {v z:V}
    (hz:z∈Z) (h:PermutationClose π b v z):v∈markedCloseSet π b Z:=
  Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(permutationClose_symm π b _ _).mp h⟩⟩

theorem subset_markedCloseSet (π:Equiv.Perm V) (b:ℕ) (Z:Finset V):Z⊆markedCloseSet π b Z:=
  fun _ hv=>mem_markedCloseSet π b Z hv (Or.inl rfl)

end Oberwolfach
