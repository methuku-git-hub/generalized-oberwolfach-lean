module

public import Oberwolfach.MarkedTerminalAbsorberAmbient
public import Oberwolfach.MarkedFixedTerminalCompletion

@[expose] public section

/-! A reserved marked absorber completes a later modified typed host.
The absorber is chosen before that host and its covering packing. The
sampled host is required only on the terminal pair, and the reserved
absorber itself must be retained. The modified host may have other edges
absent from the sampled host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_terminal_completion_in_modified_subhost
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hH:∀ v u,¬(H₀ v u∧HK v u))
    (PE:E→Prop) (PK:K→Prop) (PS:V×U→Prop) (b l s a₀ b₀ e₀ f:ℕ)
    (habs:MarkedTerminalAbsorberProperty
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val)
      (fun v u=>H₀ v u∧PS (v,u)) (fun v u=>HK v u∧PS (v,u)) π b l s a₀ b₀ e₀ f)
    (X:Finset V) (Z:Finset U) (hs:X.card+Z.card≤s)
    (F₀:Finset (Finset V⊕(V×U))) (hF:F₀.card≤f):
    ∃ C:MarkedSupportedEdgeSet
      (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ (RE:E→Prop) (RK:K→Prop) (RS:V×U→Prop),
        C.edges⊆markedSubhostResources tail head ktail khead π H₀ HK RE RK RS→
        (∀ a:E⊕K,Sum.elim RE RK a→Sum.elim tail ktail a∈X→Sum.elim head khead a∈X→Sum.elim PE PK a)→
        (∀ z:V×U,(H₀ z.1 z.2∨HK z.1 z.2)→RS z→z.1∈X→z.2∈Z→PS z)→
        MarkedRemainderDivisible tail head ktail khead HK
          (Finset.univ.filter (Sum.elim RE RK))
          (Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧RS z)) (l+4)→
        ∀ M:Finset (MarkedWheel tail head ktail khead (l+4) π b H₀ HK),
          (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
          Disjoint C.edges (M.biUnion markedWheelPhysicalResources)→
          M.biUnion markedWheelPhysicalResources⊆markedSubhostResources tail head ktail khead π H₀ HK RE RK RS→
          (∀ a:E⊕K,Sum.elim RE RK a→Sum.elim tail ktail a∉X∨Sum.elim head khead a∉X→
            Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈C.edges∪M.biUnion markedWheelPhysicalResources)→
          (∀ z:V×U,(H₀ z.1 z.2∨HK z.1 z.2)→RS z→z.1∉X∨z.2∉Z→
            Sum.inr z∈C.edges∪M.biUnion markedWheelPhysicalResources)→
          HasResourceDecomposition
            (fun W:MarkedWheel (fun e:{e // RE e}=>tail e.val) (fun e=>head e.val)
              (fun e:{e // RK e}=>ktail e.val) (fun e=>khead e.val) (l+4) π b
              (fun v u=>H₀ v u∧RS (v,u)) (fun v u=>HK v u∧RS (v,u))=>markedWheelPhysicalResources W)
            (markedSubhostResources tail head ktail khead π H₀ HK RE RK RS):=by
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=marked_terminal_absorber_in_ambient_host
    tail head ktail khead H₀ HK π PE PK PS b l s a₀ b₀ e₀ f habs X Z hs F₀ hF
  refine ⟨C,hCF,hCe,hCr,hCu,hCdec,?_⟩
  intro RE RK RS hCR hinnerA hinnerS hdiv M hM hCM hMR hcoverA hcoverS
  let A₀:=Finset.univ.filter (fun a:E⊕K=>Sum.elim PE PK a∧Sum.elim tail ktail a∈X∧Sum.elim head khead a∈X)
  let S₀:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧PS z∧z.1∈X∧z.2∈Z)
  let A:=Finset.univ.filter (Sum.elim RE RK)
  let S:=Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧RS z)
  have habs':∀ A'⊆A₀,∀ S'⊆S₀,MarkedRemainderDivisible tail head ktail khead HK A' S' (l+4)→
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W)
        (C.edges∪(A'.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S'.image Sum.inr)):=by
    intro A' hA' S' hS' hd
    exact hCabs A' S' (fun a ha=>(Finset.mem_filter.mp (hA' ha)).2)
      (fun z hz=>(Finset.mem_filter.mp (hS' hz)).2) hd
  have hiA:∀ a∈A,Sum.elim tail ktail a∈X→Sum.elim head khead a∈X→a∈A₀:=by
    intro a ha hx hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hinnerA a (Finset.mem_filter.mp ha).2 hx hy,hx,hy⟩
  have hiS:∀ z∈S,z.1∈X→z.2∈Z→z∈S₀:=by
    intro z hz hx hu
    obtain ⟨hh,hr⟩:=(Finset.mem_filter.mp hz).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh,hinnerS z hh hr hx hu,hx,hu⟩
  have hdone:=marked_fixed_terminal_completion hp hH X Z A₀ A S₀ S C.edges hCdec habs' hdiv hiA hiS hCR
    M hM hCM hMR (fun a ha hx=>hcoverA a (Finset.mem_filter.mp ha).2 hx)
    (fun z hz hx=>hcoverS z (Finset.mem_filter.mp hz).2.1 (Finset.mem_filter.mp hz).2.2 hx)
  exact marked_decomposition_restrict_to_subhost hp RE RK RS _ (Finset.Subset.refl _) hdone

end Oberwolfach
