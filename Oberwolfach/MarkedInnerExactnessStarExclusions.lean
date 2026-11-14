module

public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedPackingSpokesInHost

@[expose] public section
/-! An exact prescription of the packing's inner resources forces it to
avoid the remaining canonical inner star. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V}
  {m b:ℕ} {H₀ HK:V→U→Prop}
theorem marked_inner_exactness_implies_star_exclusions
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (I T:Finset V) (J W:Finset U) (hI:∀ x,π x∈I↔x∈I)
    (DA:Finset (E⊕K)) (DS:Finset (V×U))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hexact:(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=
      (markedFiniteResources tail head ktail khead π DA DS).filter (markedStarResource T W)):
    let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)
    let CA:=(Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I))\DA
    let CS:=(S.filter (fun z=>z.1∈I∧z.2∈J))\DS
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W);
    M.biUnion markedWheelArcs⊆Finset.univ\KA∧M.biUnion markedWheelSpokePairs⊆S\KS:=by
  intro S CA CS KA KS
  have hA:Disjoint KA (M.biUnion markedWheelArcs):=Finset.disjoint_left.mpr (by
    intro a ha hmem
    have haca: a∈CA:=(Finset.mem_filter.mp ha).1
    have hain:Sum.elim tail ktail a∈I∧Sum.elim head khead a∈I:=
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp haca).1).2
    have hnot:a∉DA:=(Finset.mem_sdiff.mp haca).2
    have hr:Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈
        (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=by
      rw [←markedPackingResources_eq_finite tail head ktail khead π M,
        ←markedFiniteResources_inner tail head ktail khead π _ _ I J hI]
      exact (markedFiniteResources_rim tail head ktail khead π hp _ _ a).mpr (Finset.mem_filter.mpr ⟨hmem,hain⟩)
    rw [hexact] at hr
    have hd:a∈DA:=(markedFiniteResources_rim tail head ktail khead π hp DA DS a).mp (Finset.mem_filter.mp hr).1
    exact hnot hd)
  have hS:Disjoint KS (M.biUnion markedWheelSpokePairs):=Finset.disjoint_left.mpr (by
    intro z hz hmem
    have hzcs:z∈CS:=(Finset.mem_filter.mp hz).1
    have hzin:z.1∈I∧z.2∈J:=(Finset.mem_filter.mp (Finset.mem_sdiff.mp hzcs).1).2
    have hnot:z∉DS:=(Finset.mem_sdiff.mp hzcs).2
    have hr:Sum.inr z∈(M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J):=by
      rw [←markedPackingResources_eq_finite tail head ktail khead π M,
        ←markedFiniteResources_inner tail head ktail khead π _ _ I J hI]
      exact (markedFiniteResources_spoke tail head ktail khead π _ _ z).mpr (Finset.mem_filter.mpr ⟨hmem,hzin⟩)
    rw [hexact] at hr
    have hd:z∈DS:=(markedFiniteResources_spoke tail head ktail khead π DA DS z).mp (Finset.mem_filter.mp hr).1
    exact hnot hd)
  exact marked_packing_disjoint_exclusions_give_host_subsets M KA KS hA hS
end Oberwolfach
