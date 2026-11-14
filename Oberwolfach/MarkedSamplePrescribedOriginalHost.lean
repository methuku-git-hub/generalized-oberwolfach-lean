module

public import Oberwolfach.MarkedSamplePrescribedPacking
public import Oberwolfach.MarkedSampleDeletionIncidences
public import Oberwolfach.MarkedSamplePhysicalDeletionLift
public import Oberwolfach.MarkedPackingResourceDetermination

@[expose] public section

/-! Pack original prescribed occurrences while avoiding actual reserved
physical graphs. The retained arc enumeration, physical resource set and
every degree bound are transported exactly back to the original host. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 40000000
set_option maxRecDepth 4096
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_sample_prescribed_packing_avoiding_graphs
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
    ∀ (DR:SimpleGraph V) (DS:SimpleGraph (V⊕U)),
    (∀ x,(DR.degree x:ℝ)≤delta*Fintype.card V)→
    (∀ x,(DS.degree (Sum.inl x):ℝ)≤delta*Fintype.card V)→
    (∀ u,(DS.degree (Sum.inr u):ℝ)≤delta*Fintype.card V)→
    let E₀:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let E₁:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E₀=>e.val.1
    let head:=fun e:E₀=>e.val.2
    let ktail:=fun e:E₁=>e.val.1
    let khead:=fun e:E₁=>e.val.2
    ∀ (X:Finset V) (J:Finset U),(∀ x,π x∈X↔x∈X)→
    ((Xᶜ).card:ℝ)≤beta*Fintype.card V/10→(J.card:ℝ)≤beta*Fintype.card V/10→
    ∀ (A:Finset (E₀⊕E₁)) (S:Finset (V×U)),
    (A.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→(S.card:ℝ)≤eta^2*(Fintype.card V:ℝ)^2→
    (∀ a∈A,Sum.elim (fun e=>s(e.val.1,e.val.2)) (fun e=>s(e.val.1,π e.val.2)) a∉DR.edgeFinset)→
    (∀ a∈A,Sum.elim tail ktail a∉X∧Sum.elim head khead a∉X)→
    (∀ v,((A.filter (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ z∈S,z.1∉X∧z.2∈J∧(H false z.1 z.2∨H true z.1 z.2))→
    (∀ z∈S,¬DS.Adj (Sum.inl z.1) (Sum.inr z.2))→
    (∀ v,((S.filter (fun z=>v=z.1)).card:ℝ)≤eta^2*Fintype.card V)→
    (∀ u,((S.filter (fun z=>z.2=u)).card:ℝ)≤eta^2*Fintype.card V)→
    ∃ M:Finset (MarkedWheel tail head ktail khead (l+4) π (3*d) (H false) (H true)),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))∧
      (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource (Xᶜ) J)=
        A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a))∪S.image Sum.inr∧
      (∀ v,((markedPackingRimGraph M).degree v:ℝ)≤24*eta*Fintype.card V)∧
      (∀ v,((Finset.univ.filter (markedPackingSpokes M v)).card:ℝ)≤6*eta*Fintype.card V)∧
      (∀ u,((Finset.univ.filter (fun v=>markedPackingSpokes M v u)).card:ℝ)≤3*(l+5)*eta*Fintype.card V) ∧
      Disjoint (markedPackingRimGraph M) DR ∧
      (∀ x u,markedPackingSpokes M x u→¬DS.Adj (Sum.inl x) (Sum.inr u)) :=by
  obtain ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,hpack⟩:=
    marked_sample_prescribed_packing_after_deletion l hl pstar gamma omega hpstar hpstar1 hg hg1 ho
  refine ⟨beta,eps,delta,eta₀,hbeta,heps,hdelta,heta₀,?_⟩
  intro eta heta hetasmall d hd
  obtain ⟨N,hN,hpack⟩:=hpack eta heta hetasmall d hd
  refine ⟨N,hN,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi DR DS hDR hDSv hDSu
  intro E₀ E₁ tail head ktail khead X J hX hXI hJ A S hAcard hScard hAavoid hArows hAdeg hS hSavoid hSrow hScol
  let emb:=markedSampleDeletedArcsEmbedding P π d σ DR.edgeFinset
  let A':=Finset.univ.filter (fun a=>emb a∈A)
  have himage:A'.image emb=A:=by
    ext a
    simp only [A',Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨a',ha',rfl⟩;exact ha'
    · intro ha
      have hrange:a∈Finset.univ.image emb:=by
        rw [markedSampleDeletedArcsEmbedding_range]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAavoid a ha⟩
      obtain ⟨a',_,he⟩:=Finset.mem_image.mp hrange
      exact ⟨a',he.symm ▸ ha,he⟩
  have hcard:A'.card=A.card:=by
    rw [←himage,Finset.card_image_of_injective _ emb.injective]
  have hfiltered (pred:E₀⊕E₁→Prop):
      (A'.filter (fun a=>pred (emb a))).card=(A.filter pred).card:=by
    rw [←himage,Finset.filter_image,Finset.card_image_of_injective _ emb.injective]
  have hend (a):Sum.elim tail ktail (emb a)=Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a ∧
      Sum.elim head khead (emb a)=Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a:=by
    cases a <;> exact ⟨rfl,rfl⟩
  have hArows' (a) (ha:a∈A'):
      Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a∉X ∧
      Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a∉X:=by
    rw [←(hend a).1,←(hend a).2]
    exact hArows (emb a) (Finset.mem_filter.mp ha).2
  have hAdeg' (v:V):((A'.filter (fun a=>v=Sum.elim (fun e=>e.val.1) (fun e=>e.val.1) a ∨
        v=Sum.elim (fun e=>e.val.2) (fun e=>e.val.2) a)).card:ℝ)≤eta^2*Fintype.card V:=by
    have he:=hfiltered (fun a=>v=Sum.elim tail ktail a∨v=Sum.elim head khead a)
    simp only [(hend _).1,(hend _).2] at he
    rw [he]
    convert hAdeg v using 1 <;> congr!
  obtain ⟨M,hM,hinner,hrim,hrow,hcol⟩:=hpack V U Γ Color hn hU P π hdeg p k q s g j hp hk hq hs σ H hr hi
    DR DS hDR hDSv hDSu X J hX hXI hJ A' S (by simpa only [hcard] using hAcard) hScard hArows' hAdeg'
    (fun z hz=>⟨(hS z hz).1,(hS z hz).2.1,by
      rcases (hS z hz).2.2 with h|h
      · exact Or.inl ⟨h,hSavoid z hz⟩
      · exact Or.inr ⟨h,hSavoid z hz⟩⟩) hSrow hScol
  let M':=M.image (markedPhysicalDeletedSampleWheelLift P π d (l+4) σ DR DS H)
  obtain ⟨hresources,hM',havoidR,havoidS⟩:=markedPhysicalDeletedSamplePacking_lift P π d (l+4) σ DR DS H M hM
  have hgraphs:=markedPackingResourceEquality_graphs M' M hresources
  have hpimage:A'.image (fun a=>(Sum.inl (markedPhysicalEdge (fun e=>e.val.1) (fun e=>e.val.2) (fun e=>e.val.1) (fun e=>e.val.2) π a):Finset V⊕(V×U)))=
      A.image (fun a=>Sum.inl (markedPhysicalEdge tail head ktail khead π a)):=by
    rw [←himage,Finset.image_image]
    apply Finset.image_congr
    intro a _
    cases a <;> rfl
  refine ⟨M',hM',?_,?_,?_,?_,havoidR,havoidS⟩
  · rw [hresources,hinner,hpimage]
  · intro x
    convert hrim x using 1
    congr 1
    exact congrArg (fun G:SimpleGraph V=>G.degree x) hgraphs.1
  · simpa only [hgraphs.2] using hrow
  · simpa only [hgraphs.2] using hcol

end Oberwolfach
