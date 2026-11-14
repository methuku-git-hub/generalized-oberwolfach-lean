module

public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section

/-! Convert the exact remaining-arc and remaining-spoke support conclusions
of active cover-down into coverage of the corresponding physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}

theorem marked_packing_covers_outside_inner
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (X:Finset V) (Z:Finset U) (A:Finset (E⊕K)) (S:Finset (V×U))
    (hA:∀ a∈A\M.biUnion markedWheelArcs,Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
    (hS:∀ s∈S\M.biUnion markedWheelSpokePairs,s.1∈X∧s.2∈Z):
    (∀ a∈A,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)∧
    (∀ s∈S,s.1∉X∨s.2∉Z→Sum.inr s∈M.biUnion markedWheelPhysicalResources):=by
  constructor
  · intro a ha hout
    have hm:a∈M.biUnion markedWheelArcs:=by
      by_contra hn
      have h:=hA a (Finset.mem_sdiff.mpr ⟨ha,hn⟩)
      exact hout.elim (fun hx=>hx h.1) (fun hx=>hx h.2)
    obtain ⟨W,hW,hw⟩:=Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨W,hW,markedWheel_arc_resource W a hw⟩
  · intro s hs hout
    have hm:s∈M.biUnion markedWheelSpokePairs:=by
      by_contra hn
      have h:=hS s (Finset.mem_sdiff.mpr ⟨hs,hn⟩)
      exact hout.elim (fun hx=>hx h.1) (fun hx=>hx h.2)
    obtain ⟨W,hW,hw⟩:=Finset.mem_biUnion.mp hm
    exact Finset.mem_biUnion.mpr ⟨W,hW,(markedWheel_spoke_resource W s).mp hw⟩

end Oberwolfach
