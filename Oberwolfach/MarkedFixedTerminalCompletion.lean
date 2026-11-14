module

public import Oberwolfach.MarkedTerminalCompletion

@[expose] public section

/-! Completion in a modified host using an absorber reserved earlier.
The modified host need only agree with the absorber's host on the terminal
resources. All final remainder identities are obtained from actual wheel
packings; no divisibility of an unspecified leftover is assumed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]
  {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_packing_resources_contained
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (A:Finset (E⊕K)) (S:Finset (V×U))
    (hM:M.biUnion markedWheelPhysicalResources⊆
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr):
    M.biUnion markedWheelArcs⊆A ∧ M.biUnion markedWheelSpokePairs⊆S:=by
  constructor
  · intro a ha
    obtain ⟨W,hW,ha⟩:=Finset.mem_biUnion.mp ha
    have he:=hM (Finset.mem_biUnion.mpr ⟨W,hW,markedWheel_arc_resource W a ha⟩)
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨a',ha',heq⟩:=Finset.mem_image.mp he
      exact hp (Sum.inl.inj heq) ▸ ha'
    · obtain ⟨s,_,heq⟩:=Finset.mem_image.mp he
      exact (Sum.inr_ne_inl heq).elim
  · intro s hs
    obtain ⟨W,hW,hs⟩:=Finset.mem_biUnion.mp hs
    have he:=hM (Finset.mem_biUnion.mpr ⟨W,hW,(markedWheel_spoke_resource W s).mp hs⟩)
    rcases Finset.mem_union.mp he with he|he
    · obtain ⟨a,_,heq⟩:=Finset.mem_image.mp he
      exact (Sum.inl_ne_inr heq).elim
    · obtain ⟨s',hs',heq⟩:=Finset.mem_image.mp he
      exact Sum.inr.inj heq ▸ hs'

theorem marked_fixed_terminal_completion
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (X:Finset V) (Z:Finset U) (A₀ A:Finset (E⊕K)) (S₀ S:Finset (V×U))
    (C:Finset (Finset V⊕(V×U)))
    (hC:HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W) C)
    (habs:∀ A'⊆A₀,∀ S'⊆S₀,MarkedRemainderDivisible tail head ktail khead HK A' S' m→
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W)
        (C∪(A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)))
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK A S m)
    (hinnerA:∀ a∈A,Sum.elim tail ktail a∈X→Sum.elim head khead a∈X→a∈A₀)
    (hinnerS:∀ s∈S,s.1∈X→s.2∈Z→s∈S₀)
    (hCR:C⊆A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (hM:∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))
    (hCM:Disjoint C (M.biUnion markedWheelPhysicalResources))
    (hMR:M.biUnion markedWheelPhysicalResources⊆
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr)
    (hcoverA:∀ a∈A,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈C∪M.biUnion markedWheelPhysicalResources)
    (hcoverS:∀ s∈S,s.1∉X∨s.2∉Z→Sum.inr s∈C∪M.biUnion markedWheelPhysicalResources):
    HasResourceDecomposition
      (fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W)
      (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr):=by
  let R:=fun W:MarkedWheel tail head ktail khead m π b H₀ HK=>markedWheelPhysicalResources W
  let T:=M.biUnion R
  let B:=A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr
  have hT:HasResourceDecomposition R T:=⟨M,hM,rfl⟩
  obtain ⟨N,hN,hNcov⟩:=resource_decomposition_union R C T hC hT hCM
  have hCT:C∪T⊆B:=Finset.union_subset hCR hMR
  have hNsub:N.biUnion markedWheelPhysicalResources⊆B:=by rwa [hNcov]
  obtain ⟨hNA,hNS⟩:=marked_packing_resources_contained hp N A S hNsub
  have hCA:∀ a∈A,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈N.biUnion markedWheelPhysicalResources:=by
    intro a ha hax
    rw [hNcov]
    exact hcoverA a ha hax
  have hCS:∀ s∈S,s.1∉X∨s.2∉Z→Sum.inr s∈N.biUnion markedWheelPhysicalResources:=by
    intro s hs hsx
    rw [hNcov]
    exact hcoverS s hs hsx
  obtain ⟨hLdiv,hLA,hLS,hLeq⟩:=marked_boundary_remainder hp hH X Z A S hdiv N hN hNA hNS hCA hCS
  let A':=A\N.biUnion markedWheelArcs
  let S':=S\N.biUnion markedWheelSpokePairs
  have hAA:A'⊆A₀:=by
    intro a ha
    exact hinnerA a (Finset.mem_sdiff.mp ha).1 (hLA a ha).1 (hLA a ha).2
  have hSS:S'⊆S₀:=by
    intro s hs
    exact hinnerS s (Finset.mem_sdiff.mp hs).1 (hLS s hs).1 (hLS s hs).2
  let L:=A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr
  have hL:L=B\(C∪T):=by
    rw [←hNcov]
    exact hLeq
  have hTL:Disjoint T L:=by
    rw [hL]
    exact Finset.disjoint_left.mpr (fun e he hf=>(Finset.mem_sdiff.mp hf).2 (Finset.mem_union_right _ he))
  have hcomplete:=resource_decomposition_union R T (C∪L) hT (habs A' hAA S' hSS hLdiv)
    (Finset.disjoint_union_right.mpr ⟨hCM.symm,hTL⟩)
  have heq:T∪(C∪L)=B:=by
    rw [hL]
    ext e
    have hh:e∈C∪T→e∈B:=fun h=>hCT h
    simp only [Finset.mem_union,Finset.mem_sdiff] at hh ⊢
    tauto
  rwa [heq] at hcomplete

end Oberwolfach
