module

public import Oberwolfach.MarkedTerminalAbsorberProperty
public import Oberwolfach.MarkedBoundaryRemainder

@[expose] public section

/-! The fixed terminal absorber completes every later wheel packing that
avoids it and covers the remaining resources outside the terminal sets.
Divisibility of the final remainder is derived by subtracting actual wheel
packings, rather than supplied as an additional assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_terminal_completion
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u)) (b l s a₀ b₀ e₀ f:ℕ)
    (habs:MarkedTerminalAbsorberProperty tail head ktail khead H₀ HK π b l s a₀ b₀ e₀ f)
    (X:Finset V) (Z:Finset U) (hs:X.card+Z.card≤s)
    (F₀:Finset (Finset V⊕(V×U))) (hF:F₀.card≤f)
    (hdiv:MarkedRemainderDivisible tail head ktail khead HK Finset.univ
      (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)) (l+4)):
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Z e)∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ M:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ HK),
        (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
        Disjoint C.edges (M.biUnion markedWheelPhysicalResources)→
        (∀ a:E⊕K,Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
          Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈C.edges∪M.biUnion markedWheelPhysicalResources)→
        (∀ z:V×U,H₀ z.1 z.2∨HK z.1 z.2→z.1∉X∨z.2∉Z→
          Sum.inr z∈C.edges∪M.biUnion markedWheelPhysicalResources)→
        HasResourceDecomposition
          (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
          (Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
            (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)).image Sum.inr) := by
  let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
  let S:=Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)
  let S₀:=S.filter (fun z=>z.1∈X∧z.2∈Z)
  have hrows:markedRemainderRows tail head ktail khead A₀ S₀⊆X:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.1
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.2
    · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2.1
  have hhubs:markedRemainderHubs S₀⊆Z:=by
    intro u hu
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hz).2.2
  have hsp:∀ z∈S₀,H₀ z.1 z.2∨HK z.1 z.2:=by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=habs X Z hs F₀ hF A₀ S₀ hrows hhubs hsp
  refine ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,?_⟩
  intro M hM hCM hcoverA hcoverS
  let R:=fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W
  let T:=M.biUnion R
  let B:=Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr
  have hT:HasResourceDecomposition R T:=⟨M,hM,rfl⟩
  obtain ⟨N,hN,hNcov⟩:=resource_decomposition_union R C.edges T hCdec hT hCM
  have hNS:N.biUnion markedWheelSpokePairs⊆S:=by
    intro z hz
    obtain ⟨W,hW,hz⟩:=Finset.mem_biUnion.mp hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    exact markedWheelPhysicalResources_spoke_present W z.1 z.2 ((markedWheel_spoke_resource W z).mp hz)
  have hCA:∀ a∈(Finset.univ:Finset (E⊕K)),Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
      Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈N.biUnion markedWheelPhysicalResources:=by
    intro a _ ha
    rw [hNcov]
    exact hcoverA a ha
  have hCS:∀ z∈S,z.1∉X∨z.2∉Z→Sum.inr z∈N.biUnion markedWheelPhysicalResources:=by
    intro z hz hx
    rw [hNcov]
    exact hcoverS z (Finset.mem_filter.mp hz).2 hx
  obtain ⟨hLdiv,hLA,hLS,hLeq⟩:=marked_boundary_remainder hp hH X Z Finset.univ S hdiv N hN
    (Finset.subset_univ _) hNS hCA hCS
  let A':=(Finset.univ:Finset (E⊕K))\N.biUnion markedWheelArcs
  let S':=S\N.biUnion markedWheelSpokePairs
  have hAA:A'⊆A₀:=by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hLA a ha⟩
  have hSS:S'⊆S₀:=by
    intro z hz
    exact Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1,hLS z hz⟩
  let L:=A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr
  have hL:L=B\(C.edges∪T):=by
    rw [← hNcov]
    exact hLeq
  have hB (W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK):R W⊆B:=by
    intro e he
    cases e with
    | inl e=>
      obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp he)
      exact Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨markedCycleTypedEdge tail head ktail khead (l+4) π b W.1 i,Finset.mem_univ _,rfl⟩)
    | inr z=>
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W z.1 z.2 he⟩,rfl⟩)
  have hCT:C.edges∪T⊆B:=by
    rw [← hNcov]
    intro e he
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
    exact hB W he
  have hTL:Disjoint T L:=by
    rw [hL]
    exact Finset.disjoint_left.mpr (fun e he hf=>(Finset.mem_sdiff.mp hf).2 (Finset.mem_union_right _ he))
  have hcomplete:=resource_decomposition_union R T (C.edges∪L) hT
    (hCabs A' hAA S' hSS hLdiv).2.2
    (Finset.disjoint_union_right.mpr ⟨hCM.symm,hTL⟩)
  have heq:T∪(C.edges∪L)=B:=by
    rw [hL]
    ext e
    have hh: e∈C.edges∪T→e∈B:=fun h=>hCT h
    simp only [Finset.mem_union,Finset.mem_sdiff] at hh ⊢
    tauto
  rwa [heq] at hcomplete

end Oberwolfach
