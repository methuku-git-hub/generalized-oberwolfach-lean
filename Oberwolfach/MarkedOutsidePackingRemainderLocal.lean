module

public import Oberwolfach.MarkedBoundaryRemainder
public import Oberwolfach.MarkedOutsideBalance

@[expose] public section

/-! Removing an actual wheel packing which covers every edge outside the
inner pair leaves a divisible graph whose remaining neighbours of outside
vertices lie in the inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
    [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_outside_packing_remainder_local
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u)) (X:Finset V) (Z:Finset U)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hArcs:∀ a:E⊕K,Sum.elim tail ktail a∉X→Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)
    (hSpokes:∀ x u,x∉X→u∉Z→H₀ x u∨HK x u→Sum.inr (x,u)∈M.biUnion markedWheelPhysicalResources)
    (hdiv:MarkedOutsideBalance tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2)) m X Z):
    let A:=Finset.univ\M.biUnion markedWheelArcs
    let S:=(Finset.univ.filter (fun s:V×U=>H₀ s.1 s.2∨HK s.1 s.2))\M.biUnion markedWheelSpokePairs;
    MarkedOutsideBalance tail head ktail khead HK A S m X Z∧
      (∀ a∈A,Sum.elim tail ktail a∉X→Sum.elim head khead a∈X)∧
      (∀ a∈A,Sum.elim head khead a∉X→Sum.elim tail ktail a∈X)∧
      (∀ s∈S,s.1∉X→s.2∈Z)∧(∀ s∈S,s.2∉Z→s.1∈X):=by
  intro A S
  have ha (a:E⊕K):a∈M.biUnion markedWheelArcs↔
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources:=by
    simp only [Finset.mem_biUnion,markedWheel_arc_resource_iff hp]
  have hs (s:V×U):s∈M.biUnion markedWheelSpokePairs↔Sum.inr s∈M.biUnion markedWheelPhysicalResources:=by
    simp only [Finset.mem_biUnion,markedWheel_spoke_resource]
  refine ⟨MarkedOutsideBalance.sdiff _ _ _ _ X Z (Finset.subset_univ _) ?_ hdiv
    (marked_packing_finite_divisible hH M hM),?_,?_,?_,?_⟩
  · intro s hs'
    obtain ⟨W,hW,hsW⟩:=Finset.mem_biUnion.mp hs'
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W s.1 s.2
      ((markedWheel_spoke_resource W s).mp hsW)⟩
  · intro a ha' hout
    by_contra hn
    exact (Finset.mem_sdiff.mp ha').2 ((ha a).mpr (hArcs a hout hn))
  · intro a ha' hout
    by_contra hn
    exact (Finset.mem_sdiff.mp ha').2 ((ha a).mpr (hArcs a hn hout))
  · intro s hs' hout
    by_contra hn
    obtain ⟨hsS,hsM⟩:=Finset.mem_sdiff.mp hs'
    exact hsM ((hs s).mpr (hSpokes s.1 s.2 hout hn (Finset.mem_filter.mp hsS).2))
  · intro s hs' hout
    by_contra hn
    obtain ⟨hsS,hsM⟩:=Finset.mem_sdiff.mp hs'
    exact hsM ((hs s).mpr (hSpokes s.1 s.2 hn hout (Finset.mem_filter.mp hsS).2))
end Oberwolfach
