module

public import Oberwolfach.MarkedSamplePrescribedOriginalHost
public import Oberwolfach.MarkedReservedResourceGraphs

@[expose] public section
/-! Prescribed marked resources can be packed while protecting a fixed small
absorber that avoids their inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem marked_sample_prescribed_packing_avoiding_reserved_resources
    (l:ℕ) (hl:2≤l) (pstar gamma omega:ℝ)
    (hpstar:0<pstar) (hpstar1:pstar≤1) (hg:0<gamma) (hg1:gamma≤1) (ho:0<omega):
    ∃ beta eps delta eta₀:ℝ,0<beta ∧ 0<eps ∧ 0<delta ∧ 0<eta₀ ∧
    ∀ eta:ℝ,0<eta→eta≤eta₀→∀ d:ℕ,1≤d→∃ N:ℕ,1≤N ∧
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    N≤Fintype.card V→ omega*Fintype.card V≤(Fintype.card U:ℝ)→
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V),
    (∀ x,(1/2+gamma/2)*Fintype.card V≤(P.degree x:ℝ))→
    ∀ (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color),
    pstar≤p→pstar≤k→(∀ u,pstar≤q u g)→(∀ u,pstar≤s u j)→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (l+12) Finset.univ p k q s g j (eps*Fintype.card V) σ H→
    MarkedIndicesWithSpokes π d (l+12) Finset.univ q s g j (eps*Fintype.card V) σ H→
    ∀ C:Finset (Finset V⊕(V×U)),(C.card:ℝ)≤delta*Fintype.card V→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (X:Finset V) (J:Finset U),(∀ x,π x∈X↔x∈X)→
    ((Xᶜ).card:ℝ)≤beta*Fintype.card V/10→(J.card:ℝ)≤beta*Fintype.card V/10→
    (∀ e∈C,¬markedInnerResource (Xᶜ) J e)→
    ∀ (A:Finset (E₀⊕E₁)) (S:Finset (V×U)),
    (A.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ z∈S,z.1∉X∧z.2∈J∧(H false z.1 z.2∨H true z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤eta^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) J)=
        A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*eta*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*eta*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*eta*Fintype.card V) ∧
      Disjoint C (M.biUnion markedWheelPhysicalResources):=by
  obtain ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,hpack⟩:=
    marked_sample_prescribed_packing_avoiding_graphs l hl pstar gamma omega hpstar hpstar1 hg hg1 ho
  refine ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,?_⟩
  intro eta heta hetasmall d hd
  obtain ⟨N,hN,hpack⟩:=hpack eta heta hetasmall d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi C hCsize
  intro E₀ E₁ tail head ktail khead X J hX hXI hJ hC A S hAcard hScard hArows hAdeg hS hSrow hScol
  let DR:=physicalEdgeGraph (markedReservedRimPairs C)
  let DS:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
  have hgraph:=marked_reserved_resource_graphs C
  have hDR:∀ x,(DR.degree x:ℝ)≤delta*Fintype.card V:=fun x=>(Nat.cast_le.mpr (hgraph.2.2.1 x)).trans hCsize
  have hDS:∀ z,(DS.degree z:ℝ)≤delta*Fintype.card V:=fun z=>(Nat.cast_le.mpr (hgraph.2.2.2 z)).trans hCsize
  have hXC:∀ x,π x∈Xᶜ↔x∈Xᶜ:=by intro x;simpa only [Finset.mem_compl] using not_congr (hX x)
  have havail:=marked_reserved_graphs_preserve_prescribed_resources tail head ktail khead π C Xᶜ J hXC hC
  have hAavoid:∀ a∈A,Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset:=by
    intro a ha
    have ha':=hArows a ha
    exact havail.1 a (Finset.mem_compl.mpr ha'.1) (Finset.mem_compl.mpr ha'.2)
  have hSavoid:∀ z∈S,¬DS.Adj (Sum.inl z.1) (Sum.inr z.2):=by
    intro z hz
    have hz':=hS z hz
    exact havail.2 z.1 (Finset.mem_compl.mpr hz'.1) z.2 hz'.2.1
  obtain ⟨M,hM,hinner,hrim,hrow,hcol,havoidR,havoidS⟩:=hpack V U Γ Color hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi
    DR DS hDR (fun x=>hDS (Sum.inl x)) (fun u=>hDS (Sum.inr u)) X J hX hXI hJ A S hAcard hScard hAavoid hArows hAdeg hS hSavoid hSrow hScol
  exact ⟨M,hM,hinner,hrim,hrow,hcol,marked_packing_avoiding_reserved_graphs (by omega) (by omega) C M havoidR havoidS⟩
end Oberwolfach
