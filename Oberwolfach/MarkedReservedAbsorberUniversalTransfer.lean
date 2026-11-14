module

public import Oberwolfach.MarkedTerminalCompletionBetweenHosts
public import Oberwolfach.MarkedReservedTerminalAbsorberProperty

@[expose] public section

/-! Select one absorber before the later host is specified. For every later
host preserving its typed resources and agreeing on the terminal pair, the
same absorber works for every divisible terminal remainder. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K]
  [DecidableEq V] [DecidableEq U] [DecidableEq E] [DecidableEq K]

theorem marked_reserved_absorber_universal_host_transfer
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop) (π:Equiv.Perm V)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (b l s a₀ b₀ e₀ f:ℕ) (ε:ℝ)
    (habs:MarkedReservedTerminalAbsorberProperty tail head ktail khead H₀ HK π b l s a₀ b₀ e₀ f ε)
    (X W:Finset V) (Z B:Finset U) (hs:X.card+Z.card≤s)
    (hX:X⊆W) (hZ:Z⊆B) (hW:(W.card:ℝ)≤ε*Fintype.card V+f) (hB:(B.card:ℝ)≤ε*Fintype.card V+f)
    (F₀:Finset (Finset V⊕(V×U))) (hF:F₀.card≤f):
    ∃ C:MarkedSupportedEdgeSet tail head ktail khead π U,
      Disjoint C.edges F₀∧C.edges.card≤e₀∧C.rows.card≤a₀∧C.hubs.card≤b₀∧
      (∀ e∈C.edges,¬MarkedOldResource tail head ktail khead π W B e)∧
      HasResourceDecomposition
        (fun Q:MarkedWheel tail head ktail khead (l+4) π b H₀ HK=>markedWheelPhysicalResources Q) C.edges∧
      ∀ (E' K':Type) [Fintype E'] [Fintype K'] [DecidableEq E'] [DecidableEq K']
        (tail' head':E'→V) (ktail' khead':K'→V) (H₀' HK':V→U→Prop),
        Function.Injective (markedPhysicalEdge tail' head' ktail' khead' π)→
        (∀ e:E,Sum.inl ({tail e,head e}:Finset V)∈C.edges→∃ e':E',tail' e'=tail e∧head' e'=head e)→
        (∀ e:K,Sum.inl ({ktail e,π (khead e)}:Finset V)∈C.edges→∃ e':K',ktail' e'=ktail e∧khead' e'=khead e)→
        (∀ v u,Sum.inr (v,u)∈C.edges→H₀ v u→H₀' v u)→
        (∀ v u,Sum.inr (v,u)∈C.edges→HK v u→HK' v u)→
        (∀ a:E'⊕K',Sum.elim tail' ktail' a∈X→Sum.elim head' khead' a∈X→
          ∃ a₀:E⊕K,Sum.elim tail ktail a₀=Sum.elim tail' ktail' a∧
            Sum.elim head khead a₀=Sum.elim head' khead' a∧markedArcType a₀=markedArcType a)→
        (∀ v∈X,∀ u∈Z,(H₀ v u↔H₀' v u)∧(HK v u↔HK' v u))→
        ∀ (A':Finset (E'⊕K')) (S':Finset (V×U)),
        (∀ a∈A',Sum.elim tail' ktail' a∈X∧Sum.elim head' khead' a∈X)→
        (∀ z∈S',z.1∈X∧z.2∈Z∧(H₀' z.1 z.2∨HK' z.1 z.2))→
        MarkedRemainderDivisible tail' head' ktail' khead' HK' A' S' (l+4)→
        IsResourceAbsorber
          (fun Q:MarkedWheel tail' head' ktail' khead' (l+4) π b H₀' HK'=>markedWheelPhysicalResources Q)
          (A'.image (fun a=>Sum.inl (markedPhysicalEdge tail' head' ktail' khead' π a))∪S'.image Sum.inr) C.edges :=by
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
  obtain ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,hCabs⟩:=habs X Z hs W B hX hZ hW hB F₀ hF A₀ S₀ hrows hhubs hsp
  refine ⟨C,hCF,hCe,hCr,hCu,hCold,hCdec,?_⟩
  intro E' K' _ _ _ _ tail' head' ktail' khead' H₀' HK' hp' hCE hCK hC₀ hCk hinnerA hinnerS A' S' hA' hS' hdiv'
  have hSA:S'⊆S₀:=by
    intro z hz
    obtain ⟨hzX,hzZ,hh⟩:=hS' z hz
    have he:=hinnerS z.1 hzX z.2 hzZ
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh.elim (fun h=>Or.inl (he.1.mpr h))
      (fun h=>Or.inr (he.2.mpr h)),hzX,hzZ⟩
  have hAA:∀ a∈A',∃ a₀∈A₀,Sum.elim tail ktail a₀=Sum.elim tail' ktail' a∧
      Sum.elim head khead a₀=Sum.elim head' khead' a∧markedArcType a₀=markedArcType a:=by
    intro a ha
    obtain ⟨hx,hy⟩:=hA' a ha
    obtain ⟨a₀,ht,hh,hj⟩:=hinnerA a hx hy
    exact ⟨a₀,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht ▸ hx,hh ▸ hy⟩,ht,hh,hj⟩
  have hSp:∀ z∈S',(H₀ z.1 z.2↔H₀' z.1 z.2)∧(HK z.1 z.2↔HK' z.1 z.2):=by
    intro z hz
    obtain ⟨hx,hu,_⟩:=hS' z hz
    exact hinnerS z.1 hx z.2 hu
  exact marked_terminal_remainder_absorption_between_hosts hp hp' A₀ A' S' C.edges
      (fun Q hQ hd=>hCabs Q hQ S' hSA hd) hdiv' hAA hSp hCE hCK hC₀ hCk
end Oberwolfach
