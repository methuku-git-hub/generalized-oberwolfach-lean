module

public import Oberwolfach.MarkedRowCoversAfterInitialRimDeletion
public import Oberwolfach.MarkedHubCoverFromWeights
public import Oberwolfach.MarkedHubPackingSupport
public import Oberwolfach.MarkedPackingStageCombination
public import Oberwolfach.MarkedHubRowProtectedBounds

@[expose] public section

/-! Construct the hub and successive-row stages in the same physical host.
Both stages are obtained from proved factor/path constructions; no packing
existence is supplied as an input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_and_row_covers_from_weights
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
    (A₀ A₁ X₀ X₁ : Fin n→Finset V) (Y₀ Y₁ : Fin n→Finset U)
    (hY : ∀ i,Disjoint (Y₀ i) (Y₁ i))
    (ain : ∀ i,(A₀ i⊕A₁ i) ↪ E⊕T) (xout : ∀ i,(X₀ i⊕X₁ i) ↪ E⊕T)
    (hinhead : ∀ i a,Sum.elim head khead (ain i a)=v i)
    (hintail : ∀ i a,Sum.elim tail ktail (ain i a)=taggedSubsetValue (A₀ i) (A₁ i) a)
    (houttail : ∀ i x,Sum.elim tail ktail (xout i x)=v i)
    (houthead : ∀ i x,Sum.elim head khead (xout i x)=taggedSubsetValue (X₀ i) (X₁ i) x)
    (hintype : ∀ i a,(ain i a).isRight=a.isRight)
    (houttype : ∀ i x,(xout i x).isRight=x.isRight)
    (hAF : ∀ i,A₀ i∪A₁ i⊆F) (hXF : ∀ i,X₀ i∪X₁ i⊆F)
    (hsepA : ∀ i z,z∈A₀ i∪A₁ i→¬PermutationClose π b z (v i))
    (hsepX : ∀ i z,z∈X₀ i∪X₁ i→¬PermutationClose π b z (v i))
    (hY₀ : ∀ i u,u∈Y₀ i→H₀ (v i) u) (hY₁ : ∀ i u,u∈Y₁ i→HK (v i) u)
    (hbalA : ∀ i,(A₀ i).card+(A₁ i).card=(Y₀ i).card+(Y₁ i).card)
    (hbalX : ∀ i,(X₀ i).card+(X₁ i).card=(Y₀ i).card+(Y₁ i).card)
    (hmarked : ∀ i,(A₁ i).card=(Y₁ i).card)
    (K : ℕ) (hK : 0<K) (degree tau lam : ℝ) (htau : 0<tau) (hlam : 0<lam)
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
      (∀ x∈F,(Finset.univ.filter (markedPackingSpokes M x)).card≤h+n*(K+4)) ∧
      (∀ z∉Finset.univ.image u,(Finset.univ.filter (fun x=>markedPackingSpokes M x z)).card≤n*(l+4)) ∧
      (∀ (I:Finset V) (J:Finset U),Disjoint F I→(∀ x,π x∈I↔x∈I)→
        (∀ i,Disjoint (Y₀ i∪Y₁ i) J)→
        (M.biUnion markedWheelPhysicalResources).filter (markedInnerResource I J)=∅) ∧
      ∀ W∈M,(W.2.val∈Finset.univ.image u∧markedWheelRows W⊆F)∨
        ∃ i,W.2.val∈Y₀ i∪Y₁ i∧markedWheelRows W⊆insert (v i) F∧v i∈markedWheelRows W := by
  obtain ⟨θ,hθ,N,hN,hcover⟩ := marked_hub_cover_from_fixed_weights (l+3) (by omega) β bLo B hβ hbLo hB
  refine ⟨θ,hθ,N,hN,?_⟩
  intro V U E T _ _ _ _ _ _ hn h n u hu hsmall tail head ktail khead π b H₀ HK c ch
    hdis hsep hsize hratio hbase hpath w hw herr
    Q hb hphys F hF v hv hvF A₀ A₁ X₀ X₁ Y₀ Y₁ hY ain xout
    hinhead hintail houttail houthead hintype houttype hAF hXF hsepA hsepX hY₀ hY₁
    hbalA hbalX hmarked K hK degree tau lam htau hlam hdeg hmargin hgap
    loss hrloss hcloss hcutloss B₁ B₂ B₃ B₄ B₅ hbudget hneighbours hYavoid
  obtain ⟨M₀,hM₀,hMcover,hMdeg,hMunique,hMpairs⟩ := hcover V U E T hn h u hu hsmall
    tail head ktail khead π b H₀ HK hb hphys hdis hsep hsize hratio
    (by simpa only [Nat.add_assoc] using hbase) hpath w hw herr
  obtain ⟨hMhubs,hMrows,hMsupport⟩ := marked_hub_cover_support M₀ u hMcover F hF hneighbours
  obtain ⟨C,hC,hcross,hCrim⟩ := marked_row_covers_after_initial_rim_deletion Q hl hb hphys F hF
    (markedPackingRimGraph M₀) hMsupport (2*h:ℕ) (by positivity)
    (by intro x;exact_mod_cast hMdeg x) v hv hvF A₀ A₁ X₀ X₁ Y₀ Y₁ hY ain xout
    hinhead hintail houttail houthead hintype houttype hAF hXF hsepA hsepX hY₀ hY₁
    hbalA hbalX hmarked K hK degree tau lam htau hlam hdeg hmargin hgap
    loss hrloss hcloss hcutloss B₁ B₂ B₃ B₄ B₅ (by intro i;have ht:=hbudget i;push_cast at ht ⊢;nlinarith only [ht])
  let required := fun i=>markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (π:=π) (ain i) (xout i) (v i) (Y₀ i∪Y₁ i)
  have hh := marked_hub_row_stages_combine (by omega) hb M₀ (Finset.univ.image u) hM₀ hMhubs
    C v F required (fun i=>Y₀ i∪Y₁ i) hC hcross hCrim hYavoid
  obtain ⟨hbr,hbs,hbc⟩:=marked_hub_row_free_degree_bounds M₀ u hMhubs hMdeg C v F required
    (fun i=>Y₀ i∪Y₁ i) hC
  refine ⟨M₀∪Finset.univ.biUnion C,hh.1,?_,hbr,hbs,?_,?_,?_⟩
  · apply Finset.Subset.trans _ hh.2
    apply Finset.union_subset_union_left
    rw [hMcover]
    exact Finset.subset_union_right
  · simpa only [Nat.add_assoc] using hbc
  · intro I J hFI hI hYJ
    exact marked_hub_row_avoids_inner (by omega) M₀ C v F I J required
      (fun i=>Y₀ i∪Y₁ i) hC hMrows hFI hI hYJ

  · intro W hW
    rcases Finset.mem_union.mp hW with hW|hW
    · exact Or.inl ⟨hMhubs W hW,hMrows W hW⟩
    · obtain ⟨i,_,hW⟩:=Finset.mem_biUnion.mp hW
      exact Or.inr ⟨i,(hC i).hubs W hW,(hC i).rows W hW,(hC i).root W hW⟩

end Oberwolfach
