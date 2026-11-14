module

public import Oberwolfach.MarkedRootPaddingConstruction

@[expose] public section

/-! The exact augmented occurrence counts and bounded support estimates.
The exceptional index set is determined by the original root graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}

def MarkedRootPair.paddedRimCount (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):ℕ:=
  Fintype.card A+Fintype.card G.Exceptional*(m+1)
def MarkedRootPair.paddedSpokeCount (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):ℕ:=
  Fintype.card S+Fintype.card G.Exceptional*(m+1)
def MarkedRootPair.paddedRowBound (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):ℕ:=
  (G.R∪G.R').card+2*Fintype.card G.Exceptional*m

@[simp] theorem MarkedRootPair.padded_rim_count (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    Fintype.card (A⊕(G.Exceptional×Fin (m+1)))=G.paddedRimCount:=by
  simp [paddedRimCount]
@[simp] theorem MarkedRootPair.padded_spoke_count (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    Fintype.card (S⊕(G.Exceptional×Fin (m+1)))=G.paddedSpokeCount:=by
  simp [paddedSpokeCount]

theorem MarkedRootPair.padded_rim_count_bound (G:MarkedRootPair tail head ktail khead H₀ HK π b m A S):
    G.paddedRimCount≤Fintype.card A*(m+2):=by
  have hi:=exceptional_marked_rows_card G.dst G.jr
  have hh:=Nat.mul_le_mul_right (m+1) hi
  change Fintype.card A+Fintype.card G.Exceptional*(m+1)≤_
  nlinarith

theorem MarkedRootPadding.rows_old_subset {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}
    (P:MarkedRootPadding G W) (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    G.R∪G.R'⊆(P.pair hm hp).R∪(P.pair hm hp).R':=by
  intro v hv;rcases Finset.mem_union.mp hv with hv|hv
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · exact Finset.mem_union_right _ (Finset.mem_union_left _ hv)

theorem MarkedRootPadding.new_rows_avoid {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}
    (P:MarkedRootPadding G W) (hm:0<m) (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    Disjoint (((P.pair hm hp).R∪(P.pair hm hp).R')\(G.R∪G.R')) W:=by
  apply Finset.disjoint_left.mpr
  intro v hv hvW
  obtain ⟨hv,hvold⟩:=Finset.mem_sdiff.mp hv
  change v∈(G.R∪pairedPaddingPrivateRows P.p false)∪(G.R'∪pairedPaddingPrivateRows P.p true) at hv
  rcases Finset.mem_union.mp hv with hv|hv
  · rcases Finset.mem_union.mp hv with hv|hv
    · exact hvold (Finset.mem_union_left _ hv)
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hi
      exact (P.avoid (false,i) k).1 hvW
  · rcases Finset.mem_union.mp hv with hv|hv
    · exact hvold (Finset.mem_union_right _ hv)
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨k,_,rfl⟩:=Finset.mem_image.mp hi
      exact (P.avoid (true,i) k).1 hvW

end Oberwolfach
