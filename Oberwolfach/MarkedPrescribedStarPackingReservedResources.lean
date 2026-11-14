module

public import Oberwolfach.MarkedPrescribedPackingReservedResources
public import Oberwolfach.MarkedFiniteResourceOperations

@[expose] public section
/-! Prescribe exactly the part of an inner resource set meeting a smaller
pair, while keeping a fixed absorber reserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_prescribed_star_packing_avoiding_reserved_resources
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
    ∀ (X T:Finset V) (J W:Finset U),(∀ x,π x∈X↔x∈X)→(∀ x,π x∈T↔x∈T)→
    ((Xᶜ).card:ℝ)≤beta*Fintype.card V/10→(J.card:ℝ)≤beta*Fintype.card V/10→
    (∀ e∈C,¬markedInnerResource (Xᶜ) J e)→
    ∀ (DA:Finset (E₀⊕E₁)) (DS:Finset (V×U)),
    let A:=DA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let S:=DS.filter (fun z=>z.1∈T∨z.2∈W);
    (A.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ z∈S,z.1∉X∧z.2∈J∧(H false z.1 z.2∨H true z.1 z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤eta^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      (∀ W₀∈M,∀ Z∈M,W₀≠Z→Disjoint (markedWheelPhysicalResources W₀) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) J)=
        (markedFiniteResources tail head ktail khead π DA DS).filter (markedStarResource T W)∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*eta*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*eta*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*eta*Fintype.card V) ∧
      Disjoint C (M.biUnion markedWheelPhysicalResources):=by
  obtain ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,hpack⟩:=
    marked_sample_prescribed_packing_avoiding_reserved_resources l hl pstar gamma omega hpstar hpstar1 hg hg1 ho
  refine ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,?_⟩
  intro eta heta hetasmall d hd
  obtain ⟨N,hN,hpack⟩:=hpack eta heta hetasmall d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi C hCsize
  intro E₀ E₁ tail head ktail khead X T J W hX hT hXI hJ hC DA DS A S hAcard hScard hArows hAdeg hS hSrow hScol
  obtain ⟨M,hM,hinner,hrim,hrow,hcol,hdis⟩:=hpack V U Γ Color hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi C hCsize X J hX hXI hJ hC A S hAcard hScard hArows hAdeg hS hSrow hScol
  refine ⟨M,hM,?_,hrim,hrow,hcol,hdis⟩
  rw [←markedFiniteResources_star tail head ktail khead π DA DS T W hT]
  exact hinner
end Oberwolfach
