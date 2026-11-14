module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! Physical avoidance of a permutation-invariant star implies the exact
auxiliary endpoint exclusions used by restricted balance identities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  [DecidableEq E] [DecidableEq K] [Fintype E] [Fintype K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_packing_finite_star_avoidance
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (I:Finset V) (J:Finset U) (hI:∀ v,π v∈I↔v∈I)
    (hstar:(M.biUnion markedWheelPhysicalResources).filter (markedStarResource I J)=∅):
    (∀ a∈M.biUnion markedWheelArcs,Sum.elim tail ktail a∉I∧Sum.elim head khead a∉I)∧
    (∀ s∈M.biUnion markedWheelSpokePairs,s.1∉I∧s.2∉J):=by
  have hnot (e:Finset V⊕(V×U)) (he:e∈M.biUnion markedWheelPhysicalResources):¬markedStarResource I J e:=by
    intro hs
    have hh:=Finset.mem_filter.mpr ⟨he,hs⟩
    rw [hstar] at hh
    exact Finset.notMem_empty e hh
  constructor
  · intro a ha
    obtain ⟨Y,hY,ha⟩:=Finset.mem_biUnion.mp ha
    have hn:=hnot (Sum.inl (markedPhysicalEdge tail head ktail khead π a))
      (Finset.mem_biUnion.mpr ⟨Y,hY,markedWheel_arc_resource Y a ha⟩)
    rw [marked_physical_rim_star_iff tail head ktail khead π I J hI] at hn
    exact not_or.mp hn
  · intro s hs
    obtain ⟨Y,hY,hs⟩:=Finset.mem_biUnion.mp hs
    have hn:=hnot (Sum.inr s)
      (Finset.mem_biUnion.mpr ⟨Y,hY,(markedWheel_spoke_resource Y s).mp hs⟩)
    exact not_or.mp hn

end Oberwolfach
