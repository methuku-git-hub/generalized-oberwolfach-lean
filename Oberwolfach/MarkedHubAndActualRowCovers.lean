module

public import Oberwolfach.MarkedHubAndRowCoversFromWeights
public import Oberwolfach.MarkedHostRowData
public import Oberwolfach.MarkedActualStarCoverage
public import Oberwolfach.MarkedHubRowFullFreeDegrees

@[expose] public section

/-! The hub-and-row construction on the current host's actual incident
arcs and spokes. Endpoint embeddings, cardinal balances and root support
are proved from the current graph, not supplied as arbitrary lists. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_and_actual_row_covers
    (l : ℕ) (hl : 2≤l) (β bLo B : ℝ) (hβ : 0<β) (hbLo : 0<bLo) (hB : 0≤B) :
    ∃ θ : ℝ,0<θ ∧ ∃ N : ℕ,1≤N ∧
    ∀ (V U E T : Type) [Fintype V] [Fintype U] [Fintype E] [Fintype T] [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V→∀ (h n : ℕ) (u : Fin h→U),Function.Injective u→
    (2*h:ℝ)≤θ*Fintype.card V→
    ∀ (tail head : E→V) (ktail khead : T→V) (π : Equiv.Perm V)
      (b : ℕ) (H₀ HK : V→U→Prop) (c ch : ℝ),
    (∀ i x,¬(H₀ x (u i)∧HK x (u i)))→
    (∀ i x z,H₀ x (u i)→HK z (u i)→x≠π z)→
    (∀ i,β*Fintype.card V≤Fintype.card (hubNeighbourClass H₀ HK (u i) true))→
    (∀ i,Fintype.card (hubNeighbourClass H₀ HK (u i) false)=
      (l+3)*Fintype.card (hubNeighbourClass H₀ HK (u i) true))→
    (∀ i,β*(Fintype.card V:ℝ)^(l+4)≤Fintype.card (HubMarkedCycle tail head ktail khead (l+3) π b H₀ HK (u i)))→
    (∀ i j,∀ x y:V,x≠y→(if j then HK x (u i) else H₀ x (u i))→
      (if j then HK y (u i) else H₀ y (u i))→
      β*(Fintype.card V:ℝ)^(l+3)≤Fintype.card
        (RootFirstCommonMarkedPath tail head ktail khead (l+3) π b H₀ HK j x y (u i) (u i)))→
    ∀ w:Fin h→MarkedCycleTuple tail head ktail khead (l+3) π b→ℝ,
    (∀ i C,bLo/(Fintype.card V:ℝ)^(l+3)≤w i C∧w i C≤B/(Fintype.card V:ℝ)^(l+3))→
    (∀ i x,H₀ x (u i)∨HK x (u i)→|1-hypergraphWeightedDegree
      (hubMarkedCycleVertices (H₀:=H₀) (Hₖ:=HK) (u i))
      (fun C=>w i (hubCycleAsMarked (u i) C)) x|≤θ)→
    ∀
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hb : 1≤b) (hphys : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F)
    (v : Fin n→V) (hv : Function.Injective v) (hvF : ∀ i,v i∉F)
    (hrowDis : ∀ i u,¬(H₀ (v i) u∧HK (v i) u))
    (hinc : ∀ i a,Sum.elim head khead a=v i→Sum.elim tail ktail a∈F)
    (hout : ∀ i a,Sum.elim tail ktail a=v i→Sum.elim head khead a∈F)
    (hsep : ∀ a:E⊕T,¬PermutationClose π b (Sum.elim tail ktail a) (Sum.elim head khead a))
    (hdir : ∀ i,(Finset.univ.filter (fun a:E⊕T=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun a:E⊕T=>Sum.elim tail ktail a=v i)).card)
    (hrow : ∀ i,(Finset.univ.filter (fun a:E⊕T=>Sum.elim head khead a=v i)).card=
      (Finset.univ.filter (fun z:V×U=>(H₀ z.1 z.2∨HK z.1 z.2)∧z.1=v i)).card)
    (hmark : ∀ i,(Finset.univ.filter (fun a:E⊕T=>Sum.elim head khead a=v i∧markedArcType a=true)).card=
      (Finset.univ.filter (fun z:V×U=>HK z.1 z.2∧z.1=v i)).card),
    let inj₀:=(markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys).1
    let injₖ:=(markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys).2
    let A₀:=fun i=>occurrenceRootNeighbours tail head (v i)
    let A₁:=fun i=>occurrenceRootNeighbours ktail khead (v i)
    let X₀:=fun i=>occurrenceRootNeighbours head tail (v i)
    let X₁:=fun i=>occurrenceRootNeighbours khead ktail (v i)
    let Y₀:=fun i=>Finset.univ.filter (H₀ (v i))
    let Y₁:=fun i=>Finset.univ.filter (HK (v i))
    let ain:=fun i=>markedNeighbourArcEmbedding tail head ktail khead inj₀ injₖ (v i)
    let xout:=fun i=>markedNeighbourArcEmbedding head tail khead ktail
      (swapped_endpoint_injective tail head inj₀) (swapped_endpoint_injective ktail khead injₖ) (v i)
    ∀ (K : ℕ) (hK : 0<K) (degree tau lam : ℝ) (htau : 0<tau) (hlam : 0<lam)
    (hdeg : 2*tau+(2*(2*b+1):ℕ)≤degree) (hmargin : (2*(2*b+1):ℕ)<lam*tau)
    (hgap : ∀ i,((X₁ i).card:ℝ)+2*tau≤(Y₀ i).card)
    (loss : ℝ) (hrloss : (n*(K+4):ℕ)≤loss) (hcloss : (n*(l+4):ℕ)≤loss)
    (hcutloss : loss≤lam*tau)
    (B₁ : ∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₁ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))
    (B₂ : ∀ i,BipartiteBlockBounds H₀ (fun a=>a∈A₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))
    (B₃ : ∀ i,BipartiteBlockBounds HK (fun a=>a∈X₁ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))
    (B₄ : ∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₀ i) (degree+loss) tau (2*lam))
    (B₅ : ∀ i,BipartiteBlockBounds H₀ (fun a=>a∈X₀ i) (fun y=>y∈Y₁ i) (degree+loss) tau (2*lam))
    (hbudget : ∀ i,((Fᶜ).card:ℝ)+(((Y₀ i).card+(Y₁ i).card)*(l+4):ℕ)/(K:ℝ)+
      (l+5)*(2*b+1)+8*(K+4:ℕ)+2*(n*(4*(K+4)):ℕ)+2*(n*(l+4):ℕ)+4*h<c),

    (∀ i x,H₀ x (u i)∨HK x (u i)→x∈F)→
    (∀ i,Disjoint (Y₀ i∪Y₁ i) (Finset.univ.image u))→
    ∃ M : Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      (∀ W∈M,∀ Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z)) ∧
      (Finset.univ.biUnion (fun i=>(Finset.univ.filter (fun x=>H₀ x (u i)∨HK x (u i))).image (fun x=>Sum.inr (x,u i))))∪
        Finset.univ.biUnion (fun i=>markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
          (π:=π) (ain i) (xout i) (v i) (Y₀ i∪Y₁ i))⊆M.biUnion markedWheelPhysicalResources ∧
      (∀ x,(spanningRestriction (markedPackingRimGraph M) F).degree x≤2*h+n*(4*(K+4))) ∧
      (∀ x∈F,(markedPackingRimGraph M).degree x≤2*h+n*(4*(K+4))+2*n) ∧
      (∀ x∈F,(Finset.univ.filter (markedPackingSpokes M x)).card≤h+n*(K+4)) ∧
      (∀ z∉Finset.univ.image u,(Finset.univ.filter (fun x=>markedPackingSpokes M x z)).card≤n*(l+4)) ∧
      (∀ (I:Finset V) (J:Finset U),Disjoint F I→(∀ x,π x∈I↔x∈I)→
        (∀ i,Disjoint (Y₀ i∪Y₁ i) J)→
        (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅) ∧
      (∀ W∈M,(W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
        ∃ i,W.2.val∈Y₀ i∪Y₁ i∧markedWheelRows W⊆insert (v i) F∧v i∈markedWheelRows W)∧
      ∀ (T':Finset V),T'⊆Finset.univ.image v→(∀ x,π x∈T'↔x∈T')→
        (∀ a:E⊕T,markedStarResource T' (Finset.univ.image u)
          (Sum.inl (markedPhysicalEdge tail head ktail khead π a))→
            Sum.inl (markedPhysicalEdge tail head ktail khead π a)∈M.biUnion markedWheelPhysicalResources)∧
        (∀ x z,H₀ x z∨HK x z→markedStarResource T' (Finset.univ.image u) (Sum.inr (x,z))→
          Sum.inr (x,z)∈M.biUnion markedWheelPhysicalResources) := by
  obtain ⟨θ,hθ,N,hN,hcover⟩:=marked_hub_and_row_covers_from_weights l hl β bLo B hβ hbLo hB
  refine ⟨θ,hθ,N,hN,?_⟩
  intro V U E T _ _ _ _ _ _ hn h n u hu hsmall tail head ktail khead π b H₀ HK c ch
    hdis hsepHub hsize hratio hbase hpath w hw herr Q hb hphys F hF v hv hvF
    hrowDis hinc hout hsep hdir hrow hmark
  dsimp only
  intro K hK degree tau lam htau hlam hdeg hmargin hgap loss hrloss hcloss hcutloss
    B₁ B₂ B₃ B₄ B₅ hbudget hneighbours hYavoid
  obtain ⟨inj₀,injₖ⟩:=markedPhysicalEdge_endpoint_injections tail head ktail khead π hphys
  have hA (i:Fin n):=
    marked_neighbour_support_and_separation tail head ktail khead π b (v i) F (hinc i)
      (by intro a ha;rw [←ha];exact hsep a)
  have hX (i:Fin n):=
    marked_neighbour_support_and_separation head tail khead ktail π b (v i) F (hout i)
      (by
        intro a ha hc
        apply hsep a
        rw [ha]
        exact (permutationClose_symm π b _ _).mp hc)
  have hbalance (i:Fin n):=marked_neighbour_row_balances tail head ktail khead H₀ HK (v i)
    inj₀ injₖ (hrowDis i) (hdir i) (hrow i) (hmark i)
  obtain ⟨M,hM,hcov,hbr,hbs,hbc,hinner,hsupport⟩:=hcover V U E T hn h n u hu hsmall tail head ktail khead π b H₀ HK c ch
    hdis hsepHub hsize hratio hbase hpath w hw herr Q hb hphys F hF v hv hvF
    (fun i=>occurrenceRootNeighbours tail head (v i))
    (fun i=>occurrenceRootNeighbours ktail khead (v i))
    (fun i=>occurrenceRootNeighbours head tail (v i))
    (fun i=>occurrenceRootNeighbours khead ktail (v i))
    (fun i=>Finset.univ.filter (H₀ (v i))) (fun i=>Finset.univ.filter (HK (v i)))
    (fun i=>marked_actual_spoke_rows_disjoint H₀ HK (v i) (hrowDis i))
    (fun i=>markedNeighbourArcEmbedding tail head ktail khead inj₀ injₖ (v i))
    (fun i=>markedNeighbourArcEmbedding head tail khead ktail
      (swapped_endpoint_injective tail head inj₀) (swapped_endpoint_injective ktail khead injₖ) (v i))
    (fun i=>markedNeighbourArcEmbedding_root _ _ _ _ _ _ _)
    (fun i=>markedNeighbourArcEmbedding_first _ _ _ _ _ _ _)
    (fun i=>markedNeighbourArcEmbedding_root _ _ _ _ _ _ _)
    (fun i=>markedNeighbourArcEmbedding_first _ _ _ _ _ _ _)
    (fun i=>markedNeighbourArcEmbedding_type _ _ _ _ _ _ _)
    (fun i=>markedNeighbourArcEmbedding_type _ _ _ _ _ _ _)
    (fun i=>(hA i).1) (fun i=>(hX i).1) (fun i=>(hA i).2) (fun i=>(hX i).2)
    (by intro i u hu;exact (Finset.mem_filter.mp hu).2)
    (by intro i u hu;exact (Finset.mem_filter.mp hu).2)
    (fun i=>(hbalance i).1) (fun i=>(hbalance i).2.1) (fun i=>(hbalance i).2.2)
    K hK degree tau lam htau hlam hdeg hmargin hgap loss hrloss hcloss hcutloss
    B₁ B₂ B₃ B₄ B₅ hbudget hneighbours hYavoid

  have hrowsAll:∀ W∈M,markedWheelRows W⊆F∪Finset.univ.image v:=by
    intro W hW x hx
    rcases hsupport W hW with ⟨_,hrows⟩|⟨i,_,hrows,_⟩
    · exact Finset.mem_union_left _ (hrows hx)
    · rcases Finset.mem_insert.mp (hrows hx) with he|he
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he.symm⟩)
      · exact Finset.mem_union_left _ he
  have hfull:=marked_hub_row_full_free_rim_degree M v F hF hrowsAll _ hbr
  refine ⟨M,hM,hcov,hbr,hfull,hbs,hbc,hinner,hsupport,?_⟩
  intro T' hTv hT'
  apply marked_actual_star_covered tail head ktail khead π H₀ HK inj₀ injₖ n h v u T' hTv hT'
    (M.biUnion markedWheelPhysicalResources)
  · intro i x hx
    apply hcov
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ _,Finset.mem_image.mpr
      ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hx⟩,rfl⟩⟩
  · intro i r hr
    apply hcov
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hr⟩)

end Oberwolfach
