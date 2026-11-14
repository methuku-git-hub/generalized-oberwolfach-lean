module

public import Oberwolfach.MarkedReservedTerminalAbsorberProperty

@[expose] public section

/-! Choose one reservoir for all divisible remainders on a fixed terminal
pair, before the later completion host is selected. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U]

theorem marked_choose_reserved_terminal_reservoir
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (b l s a₀ b₀ e₀ f:ℕ) (ε:ℝ)
    (habs:MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π b l s a₀ b₀ e₀ f ε)
    (X:Finset V) (Z:Finset U) (hs:X.card+Z.card≤s)
    (W:Finset V) (B:Finset U) (hXW:X⊆W) (hZB:Z⊆B)
    (hW:(W.card:ℝ)≤ε*Fintype.card V+f) (hB:(B.card:ℝ)≤ε*Fintype.card V+f)
    (F₀:Finset (Finset V⊕(V×U))) (hF:F₀.card≤f):
    let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
    let S₀:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1∈X∧z.2∈Z);
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀ ∧ C.edges.card≤e₀ ∧ C.rows.card≤a₀ ∧ C.hubs.card≤b₀ ∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e) ∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges ∧
      ∀ A⊆A₀,∀ S⊆S₀,MarkedRemainderDivisible tail head ktail khead HK A S (l+4)→
        IsResourceAbsorber
          (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
          (A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr) C.edges := by
  let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
  let S₀:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1∈X∧z.2∈Z)
  have hrows:markedRemainderRows tail head ktail khead A₀ S₀⊆X:=by
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · rcases Finset.mem_union.mp hv with hv|hv
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.1
      · obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp ha).2.2
    · obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hz).2.2.1
  have hhubs:markedRemainderHubs S₀⊆Z:=by
    intro u hu
    obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hu
    exact (Finset.mem_filter.mp hz).2.2.2
  have hsp:∀ z∈S₀,H₀ z.1 z.2∨HK z.1 z.2:=fun z hz=>(Finset.mem_filter.mp hz).2.1
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=habs X Z hs W B hXW hZB hW hB F₀ hF A₀ S₀ hrows hhubs hsp
  exact ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩
end Oberwolfach
