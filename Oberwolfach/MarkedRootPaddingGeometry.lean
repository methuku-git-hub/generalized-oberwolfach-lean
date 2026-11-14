module

public import Oberwolfach.MarkedRootPaddingSizes

@[expose] public section

/-! Remove padding from the geometric separation conclusions without
requiring global separation within either original root set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A S:Type} [Fintype V] [Fintype U] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b m:ℕ}
    {G:MarkedRootPair tail head ktail khead H₀ HK π b m A S} {W:Finset V}

theorem MarkedRootPadding.new_row_private (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (v:V)
    (hv:v∈((P.pair hm hp).R∪(P.pair hm hp).R')\(G.R∪G.R')):
    ∃ i:Bool×G.Exceptional,∃ k:Fin m,v=P.p i k:=by
  obtain ⟨hv,hvold⟩:=Finset.mem_sdiff.mp hv
  change v∈(G.R∪pairedPaddingPrivateRows P.p false)∪(G.R'∪pairedPaddingPrivateRows P.p true) at hv
  rcases Finset.mem_union.mp hv with hv|hv
  · rcases Finset.mem_union.mp hv with hv|hv
    · exact (hvold (Finset.mem_union_left _ hv)).elim
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hi
      exact ⟨(false,i),k,hk.symm⟩
  · rcases Finset.mem_union.mp hv with hv|hv
    · exact (hvold (Finset.mem_union_right _ hv)).elim
    · obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp hv
      obtain ⟨k,_,hk⟩:=Finset.mem_image.mp hi
      exact ⟨(true,i),k,hk.symm⟩

theorem MarkedRootPadding.extended_rows_separated (P:MarkedRootPadding G W) (hm:0<m)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π)) (X:Finset V)
    (hroot:∀ x∈X\((P.pair hm hp).R∪(P.pair hm hp).R'),∀ y∈(P.pair hm hp).R∪(P.pair hm hp).R',
      ¬PermutationClose π b x y)
    (hfree:∀ x∈X\((P.pair hm hp).R∪(P.pair hm hp).R'),∀ y∈X\((P.pair hm hp).R∪(P.pair hm hp).R'),
      x≠y→¬PermutationClose π b x y):
    (∀ x∈X\(G.R∪G.R'),∀ y∈G.R∪G.R',¬PermutationClose π b x y)∧
    (∀ x∈X\(G.R∪G.R'),∀ y∈X\(G.R∪G.R'),x≠y→¬PermutationClose π b x y):=by
  constructor
  · intro x hx y hy
    obtain ⟨hx,hxo⟩:=Finset.mem_sdiff.mp hx
    by_cases hxp:x∈(P.pair hm hp).R∪(P.pair hm hp).R'
    · obtain ⟨i,k,rfl⟩:=P.new_row_private hm hp x (Finset.mem_sdiff.mpr ⟨hxp,hxo⟩)
      exact (P.avoid i k).2.2 y hy
    · exact hroot x (Finset.mem_sdiff.mpr ⟨hx,hxp⟩) y (P.rows_old_subset hm hp hy)
  · intro x hx y hy hxy
    obtain ⟨hx,hxo⟩:=Finset.mem_sdiff.mp hx
    obtain ⟨hy,hyo⟩:=Finset.mem_sdiff.mp hy
    by_cases hxp:x∈(P.pair hm hp).R∪(P.pair hm hp).R'
    · by_cases hyp:y∈(P.pair hm hp).R∪(P.pair hm hp).R'
      · obtain ⟨i,k,rfl⟩:=P.new_row_private hm hp x (Finset.mem_sdiff.mpr ⟨hxp,hxo⟩)
        obtain ⟨j,k',rfl⟩:=P.new_row_private hm hp y (Finset.mem_sdiff.mpr ⟨hyp,hyo⟩)
        exact P.separatedPaths i j k k' hxy
      · intro hc
        exact hroot y (Finset.mem_sdiff.mpr ⟨hy,hyp⟩) x hxp ((permutationClose_symm π b _ _).mp hc)
    · by_cases hyp:y∈(P.pair hm hp).R∪(P.pair hm hp).R'
      · exact hroot x (Finset.mem_sdiff.mpr ⟨hx,hxp⟩) y hyp
      · exact hfree x (Finset.mem_sdiff.mpr ⟨hx,hxp⟩) y (Finset.mem_sdiff.mpr ⟨hy,hyp⟩) hxy

end Oberwolfach
