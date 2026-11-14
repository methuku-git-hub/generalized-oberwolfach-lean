module

public import Oberwolfach.MarkedTerminalRemainderHostTransfer
public import Oberwolfach.MarkedFixedTerminalCompletion

@[expose] public section

/-! The terminal-completion interface for separate sampled and modified
hosts. Their arc sets may differ away from the reserved absorber and the
terminal pair. The reservoir is fixed before the modified host and its
covering packing; final divisibility is proved by subtraction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_wheel_resources_in_full_host
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V) (m b:ℕ)
    (W:MarkedWheel tail head ktail khead m π b H₀ HK):
    markedWheelPhysicalResources W⊆
      Finset.univ.image (fun a:E⊕K=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪
        (Finset.univ.filter (fun z:V×U=>H₀ z.1 z.2∨HK z.1 z.2)).image Sum.inr:=by
  intro e he
  cases e with
  | inl e=>
    obtain ⟨i,hi,rfl⟩:=Finset.mem_image.mp ((markedWheelPhysicalResources_rim W e).mp he)
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨markedCycleTypedEdge tail head ktail khead m π b W.1 i,Finset.mem_univ _,rfl⟩)
  | inr z=>
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,markedWheelPhysicalResources_spoke_present W z.1 z.2 he⟩,rfl⟩)

theorem marked_terminal_completion_between_hosts
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (b l s a₀ b₀ e₀ f:ℕ)
    (habs:MarkedTerminalAbsorberProperty tail head ktail khead H₀ HK π b l s a₀ b₀ e₀ f)
    (X:Finset V) (Z:Finset U) (hs:X.card+Z.card≤s)
    (F₀:Finset (Finset V⊕(V×U))) (hF:F₀.card≤f):
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π X Z e)∧
      HasResourceDecomposition
        (fun W:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources W) C.edges∧
      ∀ (E' K':Type) [Fintype E'] [Fintype K'] [DecidableEq E'] [DecidableEq K']
        (tail' head':E'→V) (ktail' khead':K'→V) (H₀' HK':V→U→Prop),
        Function.Injective (markedPhysicalEdge tail' head' ktail' khead' π)→
        (∀ v u,¬(H₀' v u∧HK' v u))→
        (∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C.edges→∃ e':E',tail' e'=tail e∧head' e'=head e)→
        (∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C.edges→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e)→
        (∀ v u,Sum.inr (v,u)∈C.edges→H₀ v u→H₀' v u)→
        (∀ v u,Sum.inr (v,u)∈C.edges→HK v u→HK' v u)→
        (∀ a:E'⊕K',Sum.elim tail' ktail' a∈X→Sum.elim head' khead' a∈X→
          ∃ a₀:E⊕K,Sum.elim tail ktail a₀=Sum.elim tail' ktail' a∧
            Sum.elim head khead a₀=Sum.elim head' khead' a∧markedArcType a₀=markedArcType a)→
        (∀ v∈X,∀ u∈Z,(H₀ v u↔H₀' v u)∧(HK v u↔HK' v u))→
        MarkedRemainderDivisible tail' head' ktail' khead' HK' Finset.univ
          (Finset.univ.filter (fun z:V×U=>H₀' z.1 z.2∨HK' z.1 z.2)) (l+4)→
        ∀ M:Finset (MarkedWheel tail' head' ktail' khead' (l+4) π b H₀' HK'),
          (∀ W∈M,∀ W'∈M,W≠W'→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources W'))→
          Disjoint C.edges (M.biUnion markedWheelPhysicalResources)→
          (∀ a:E'⊕K',Sum.elim tail' ktail' a∉X∨Sum.elim head' khead' a∉X→
            Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a)∈C.edges∪M.biUnion markedWheelPhysicalResources)→
          (∀ z:V×U,(H₀' z.1 z.2∨HK' z.1 z.2)→z.1∉X∨z.2∉Z→
            Sum.inr z∈C.edges∪M.biUnion markedWheelPhysicalResources)→
          HasResourceDecomposition
            (fun W:MarkedWheel tail' head' ktail' khead' (l+4) π b H₀' HK'=>markedWheelPhysicalResources W)
            (Finset.univ.image (fun a:E'⊕K'=>Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))∪
              (Finset.univ.filter (fun z:V×U=>H₀' z.1 z.2∨HK' z.1 z.2)).image Sum.inr):=by
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
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=habs X Z hs F₀ hF A₀ S₀ hrows hhubs hsp
  refine ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,?_⟩
  intro E' K' _ _ _ _ tail' head' ktail' khead' H₀' HK' hp' hH'
    hCE hCK hC₀ hCk hinnerA hinnerS hdiv M hM hCM hcoverA hcoverS
  let A₁:=Finset.univ.filter (fun a:E'⊕K'=>Sum.elim tail' ktail' a∈X∧Sum.elim head' khead' a∈X)
  let S:=Finset.univ.filter (fun z:V×U=>H₀' z.1 z.2∨HK' z.1 z.2)
  let S₁:=S.filter (fun z=>z.1∈X∧z.2∈Z)
  have hCdec':HasResourceDecomposition
      (fun W:MarkedWheel tail' head' ktail' khead' (l+4) π b H₀' HK'=>markedWheelPhysicalResources W) C.edges:=
    marked_decomposition_transfer_on_resources C.edges hCE hCK hC₀ hCk hCdec
  have hAbs':∀ A'⊆A₁,∀ S'⊆S₁,MarkedRemainderDivisible tail' head' ktail' khead' HK' A' S' (l+4)→
      HasResourceDecomposition
        (fun W:MarkedWheel tail' head' ktail' khead' (l+4) π b H₀' HK'=>markedWheelPhysicalResources W)
        (C.edges∪(A'.image (fun a=>Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))∪S'.image Sum.inr)):=by
    intro A' hA' S' hS' hdiv'
    have hSA:S'⊆S₀:=by
      intro z hz
      obtain ⟨hzS,hzX,hzZ⟩:=Finset.mem_filter.mp (hS' hz)
      have hh:=(Finset.mem_filter.mp hzS).2
      have he:=hinnerS z.1 hzX z.2 hzZ
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.elim (fun h=>Or.inl (he.1.mpr h))
        (fun h=>Or.inr (he.2.mpr h)),hzX,hzZ⟩
    have hAA:∀ a∈A',∃ a₀∈A₀,Sum.elim tail ktail a₀=Sum.elim tail' ktail' a∧
        Sum.elim head khead a₀=Sum.elim head' khead' a∧markedArcType a₀=markedArcType a:=by
      intro a ha
      obtain ⟨hx,hy⟩:=(Finset.mem_filter.mp (hA' ha)).2
      obtain ⟨a₀,ht,hh,hj⟩:=hinnerA a hx hy
      exact ⟨a₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht ▸ hx,hh ▸ hy⟩,ht,hh,hj⟩
    have hSp:∀ z∈S',(H₀ z.1 z.2↔H₀' z.1 z.2)∧(HK z.1 z.2↔HK' z.1 z.2):=by
      intro z hz
      obtain ⟨_,hx,hu⟩:=Finset.mem_filter.mp (hS' hz)
      exact hinnerS z.1 hx z.2 hu
    exact (marked_terminal_remainder_absorption_between_hosts hp hp' A₀ A' S' C.edges
      (fun B hB hd=>hCabs B hB S' hSA hd) hdiv' hAA hSp hCE hCK hC₀ hCk).2.2
  let R:=Finset.univ.image (fun a:E'⊕K'=>Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))∪S.image Sum.inr
  have hW (W:MarkedWheel tail' head' ktail' khead' (l+4) π b H₀' HK'):markedWheelPhysicalResources W⊆R:=
    marked_wheel_resources_in_full_host tail' head' ktail' khead' H₀' HK' π (l+4) b W
  have hCR:C.edges⊆R:=by
    obtain ⟨N,_,hN⟩:=hCdec'
    rw [←hN]
    intro e he
    obtain ⟨W,_,he⟩:=Finset.mem_biUnion.mp he
    exact hW W he
  have hMR:M.biUnion markedWheelPhysicalResources⊆R:=by
    intro e he
    obtain ⟨W,_,he⟩:=Finset.mem_biUnion.mp he
    exact hW W he
  exact marked_fixed_terminal_completion hp' hH' X Z A₁ Finset.univ S₁ S C.edges hCdec' hAbs' hdiv
    (fun a ha hx hy=>Finset.mem_filter.mpr ⟨ha,hx,hy⟩)
    (fun z hz hx hu=>Finset.mem_filter.mpr ⟨hz,hx,hu⟩) hCR M hM hCM hMR
    (fun a _ hx=>hcoverA a hx) (fun z hz hx=>hcoverS z (Finset.mem_filter.mp hz).2 hx)

end Oberwolfach
