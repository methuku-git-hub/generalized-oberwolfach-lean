module

public import Oberwolfach.MarkedPrescribedStarPackingReservedResources
public import Oberwolfach.MarkedFiniteResourceOperations
public import Oberwolfach.MarkedReservedPrescribedDeepBalanced
public import Oberwolfach.MarkedReservedDeletionBudget
public import Oberwolfach.MarkedReservedCanonicalDeletionGraphs
public import Oberwolfach.MarkedReservedCanonicalCombinedBalance

@[expose] public section
/-! Prescribe exactly the part of an inner resource set meeting a smaller
pair, while keeping a fixed absorber reserved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_prescribed_star_to_balanced_deep_host
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
    ∀ (X T:Finset V) (J W:Finset U),(∀ x,π x∈X↔x∈X)→(∀ x,π x∈T↔x∈T)→T⊆Xᶜ→W⊆J→
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
    let Full:=Finset.univ.filter (fun z:V×U=>H false z.1 z.2∨H true z.1 z.2)
    let CA:=(Finset.univ.filter (fun a:E₀⊕E₁=>Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ))\DA
    let CS:=(Full.filter (fun z=>z.1∈Xᶜ∧z.2∈J))\DS
    let KA:=CA.filter (fun a=>Sum.elim tail ktail a∈T∨Sum.elim head khead a∈T)
    let KS:=CS.filter (fun z=>z.1∈T∨z.2∈W);
    (∀ v u,¬(H false v u∧H true v u))→
    MarkedRemainderDivisible tail head ktail khead (H true) Finset.univ Full (l+4)→
    HasResourceDecomposition (fun Y:MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)=>markedWheelPhysicalResources Y) C→
    MarkedRemainderDivisible tail head ktail khead (H true) CA CS (l+4)→
    (∀ a∈DA,Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ)→
    (∀ z∈DS,z.1∈Xᶜ∧z.2∈J∧z∈Full)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      (∀ Y∈M,∀ Z∈M,Y≠Z→Disjoint (markedWheelPhysicalResources Y) (markedWheelPhysicalResources Z))∧
      (∀ x,((markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)).degree x:ℝ)≤(Xᶜ).card+24*eta*Fintype.card V)∧
      (∀ x,((markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)).degree (Sum.inl x):ℝ)≤J.card+6*eta*Fintype.card V)∧
      (∀ u,((markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)).degree (Sum.inr u):ℝ)≤(Xᶜ).card+3*(l+5)*eta*Fintype.card V)∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*eta*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*eta*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*eta*Fintype.card V)∧
      Disjoint C (M.biUnion markedWheelPhysicalResources)∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) J)=
        (markedFiniteResources tail head ktail khead π DA DS).filter (markedStarResource T W)∧
    let DR:=physicalEdgeGraph (markedReservedRimPairs C)
    let DReserved:=markedFiniteSpokeGraph (markedReservedSpokePairs C)
    let σ':=rawMarkedDeleteRims σ DR.edgeFinset
    let H':=markedDeletePhysicalSpokes H DReserved
    let E':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) false
    let K':=MarkedSampleArc P π (3*d) (fun e=>σ' (Sum.inl e)) true
    let t':=fun e:E'=>e.val.1
    let h':=fun e:E'=>e.val.2
    let kt':=fun e:K'=>e.val.1
    let kh':=fun e:K'=>e.val.2
    let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
    let DA':=Finset.univ.filter (fun a:E'⊕K'=>emb a∈DA)
    let S':=Finset.univ.filter (fun z:V×U=>H' false z.1 z.2∨H' true z.1 z.2)
    let CA':=(Finset.univ.filter (fun a:E'⊕K'=>Sum.elim t' kt' a∈Xᶜ∧Sum.elim h' kh' a∈Xᶜ))\DA'
    let CS':=(S'.filter (fun z=>z.1∈Xᶜ∧z.2∈J))\DS
    let KA':=CA'.filter (fun a=>Sum.elim t' kt' a∈T∨Sum.elim h' kh' a∈T)
    let KS':=CS'.filter (fun z=>z.1∈T∨z.2∈W);
    ∃ M':Finset (MarkedWheel t' h' kt' kh' (l+4) π (3*d) (H' false) (H' true)),
      (∀ X∈M',∀ Y∈M',X≠Y→Disjoint (markedWheelPhysicalResources X) (markedWheelPhysicalResources Y))∧
      M'.biUnion markedWheelPhysicalResources=M.biUnion markedWheelPhysicalResources∧
      markedSampleArcSetGraph P π d σ' (KA'∪M'.biUnion markedWheelArcs)=
        markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs)∧
      markedFiniteSpokeGraph (KS'∪M'.biUnion markedWheelSpokePairs)=
        markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)∧
      (∀ x,(markedPackingRimGraph M').degree x=(markedPackingRimGraph M).degree x)∧
      (∀ x,(Finset.univ.filter (markedPackingSpokes M' x)).card=(Finset.univ.filter (markedPackingSpokes M x)).card)∧
      (∀ u,(Finset.univ.filter (fun x=>markedPackingSpokes M' x u)).card=
        (Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card)∧
      let DR₂:=markedSampleArcSetGraph P π d σ' (KA'∪M'.biUnion markedWheelArcs)
      let DS₂:=markedFiniteSpokeGraph (KS'∪M'.biUnion markedWheelSpokePairs)
      let σ₂:=rawMarkedDeleteRims σ' DR₂.edgeFinset
      let H₂:=markedDeletePhysicalSpokes H' DS₂
      let E₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) false
      let K₂:=MarkedSampleArc P π (3*d) (fun e=>σ₂ (Sum.inl e)) true
      let src₂:=Sum.elim (fun e:E₂=>e.val.1) (fun e:K₂=>e.val.1)
      let dst₂:=Sum.elim (fun e:E₂=>e.val.2) (fun e:K₂=>e.val.2);
      (∀ v∈T,
        (Finset.univ.filter (fun a=>dst₂ a=v)).card=(Finset.univ.filter (fun a=>src₂ a=v)).card ∧
        (Finset.univ.filter (fun a=>dst₂ a=v)).card=
          (Finset.univ.filter (fun z:V×U=>(H₂ false z.1 z.2∨H₂ true z.1 z.2)∧z.1=v)).card ∧
        (Finset.univ.filter (fun a=>dst₂ a=v∧markedArcType a=true)).card=
          (Finset.univ.filter (fun z:V×U=>H₂ true z.1 z.2∧z.1=v)).card) ∧
      (∀ u∈W,Fintype.card (hubNeighbourClass (H₂ false) (H₂ true) u false)=
        (l+4)*Fintype.card (hubNeighbourClass (H₂ false) (H₂ true) u true)) ∧
      (∀ a:E₂⊕K₂,dst₂ a∈T→src₂ a∉Xᶜ) ∧
      (∀ a:E₂⊕K₂,src₂ a∈T→dst₂ a∉Xᶜ) ∧
      (∀ x∈T,∀ u,H₂ false x u∨H₂ true x u→u∉J) ∧
      (∀ u∈W,∀ x,H₂ false x u∨H₂ true x u→x∉Xᶜ) ∧
      let Dall:=markedSampleArcSetGraph P π d σ (KA∪M.biUnion markedWheelArcs) ⊔ DR
      let edgeAll:Fintype Dall.edgeSet:=@SimpleGraph.fintypeEdgeSet V Dall (Sym2.instFintype)
        (fun x y=>Classical.propDecidable (Dall.Adj x y));
      MarkedDeepHostBalanced P π d (l+4) (rawMarkedDeleteRims σ (@SimpleGraph.edgeFinset V Dall edgeAll))
        (markedDeletePhysicalSpokes H (markedFiniteSpokeGraph (KS∪M.biUnion markedWheelSpokePairs)⊔DReserved)) Xᶜ T J W:=by
  obtain ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,hpack⟩:=
    marked_sample_prescribed_star_packing_avoiding_reserved_resources l hl pstar gamma omega hpstar hpstar1 hg hg1 ho
  refine ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,?_⟩
  intro eta heta hetasmall d hd
  obtain ⟨N,hN,hpack⟩:=hpack eta heta hetasmall d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi C hCsize
  intro E₀ E₁ tail head ktail khead X T J W hX hT hTI hWJ hXI hJ hC DA DS A S hAcard hScard hArows hAdeg hS hSrow hScol Full CA CS KA KS hH hOuter hDec hInner hDA hDS
  obtain ⟨M,hM,hinner,hrim,hrow,hcol,hdis⟩:=hpack V U Γ Color hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi C hCsize X T J W hX hT hXI hJ hC DA DS hAcard hScard hArows hAdeg hS hSrow hScol
  have hI:∀ x,π x∈Xᶜ↔x∈Xᶜ:=by intro x;simpa only [Finset.mem_compl] using not_congr (hX x)
  have hKA:∀ a∈KA,Sum.elim tail ktail a∈Xᶜ∧Sum.elim head khead a∈Xᶜ:=by
    intro a ha
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1).2
  have hKS:∀ z∈KS,z.1∈Xᶜ∧z.2∈J:=by
    intro z hz
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp (Finset.mem_filter.mp hz).1).1).2
  have hbudget:=marked_reserved_packing_deletion_bounds P π d (l+4) σ H Xᶜ J hI KA KS hKA hKS M
    (24*eta*Fintype.card V) (6*eta*Fintype.card V) (3*(l+5)*eta*Fintype.card V) hrim hrow hcol
  refine ⟨M,hM,hbudget.1,hbudget.2.1,hbudget.2.2,hrim,hrow,hcol,hdis,hinner,?_⟩
  obtain ⟨M',hM',hres,hdegR,hdegV,hdegU,hbalanced⟩:=
    marked_reserved_prescribed_deep_host_balanced P π d (l+4) σ H C Xᶜ T J W hTI hWJ hI hT hC DA DS hH hOuter hDec hInner hDS M hM hdis hDA hinner
  have hgraphs:=marked_reserved_canonical_deletion_graphs_equal P π d (l+4) σ H C Xᶜ T J W hI hC DA DS M M' hres
  have hbalanced':MarkedDeepHostBalanced P π d (l+4) _ _ Xᶜ T J W:=hbalanced
  have hcombined:=marked_reserved_canonical_combined_deep_balance P π d (l+4) σ H C Xᶜ T J W hI hC DA DS M M' hres hbalanced'
  exact ⟨M',hM',hres,hgraphs.1,hgraphs.2,hdegR,hdegV,hdegU,hbalanced.1,hbalanced.2.1,
    hbalanced.2.2.1,hbalanced.2.2.2.1,hbalanced.2.2.2.2.1,hbalanced.2.2.2.2.2,hcombined⟩
end Oberwolfach
