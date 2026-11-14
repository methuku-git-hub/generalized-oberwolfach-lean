module

public import Oberwolfach.MarkedRowCoverOnLabelledParts
public import Oberwolfach.TaggedSubsetEmbedding
public import Oberwolfach.MarkedRootArcRestriction
public import Oberwolfach.MarkedRestrictedFamilyIdentities
public import Oberwolfach.MarkedSpokeDeletionExtensions
public import Oberwolfach.BipartiteBlockAfterDeletion

@[expose] public section

/-! A row cover after arbitrary bounded realized deletions inside the free
set. The construction retains every supplied root arc and root spoke. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {b l : ℕ} {c ch : ℝ}

theorem marked_row_cover_after_free_deletion
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (hb : 1≤b) (hphys : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F) (v : V) (hv : v∉F)
    (D : SimpleGraph V) (hDF : GraphSupportedOn F D)
    (J : V→U→Prop) (hJF : ∀ x u,J x u→x∈F)
    (delta : ℝ) (hdelta : 0≤delta) (hD : ∀ x,(D.degree x:ℝ)≤delta)
    (drow dcol : ℕ) (hJrow : ∀ x,(Finset.univ.filter (J x)).card≤drow)
    (hJcol : ∀ u,(Finset.univ.filter (fun x=>J x u)).card≤dcol)
    (loss : ℝ) (hrloss : (drow:ℝ)≤loss) (hcloss : (dcol:ℝ)≤loss)
    (A₀ A₁ X₀ X₁ : Finset V) (Y₀ Y₁ : Finset U) (hY : Disjoint Y₀ Y₁)
    (hincoming : (A₀⊕A₁) ↪ E⊕T) (houtgoing : (X₀⊕X₁) ↪ E⊕T)
    (hinhead : ∀ a, Sum.elim head khead (hincoming a)=v)
    (hintail : ∀ a, Sum.elim tail ktail (hincoming a)=taggedSubsetValue A₀ A₁ a)
    (houttail : ∀ x, Sum.elim tail ktail (houtgoing x)=v)
    (houthead : ∀ x, Sum.elim head khead (houtgoing x)=taggedSubsetValue X₀ X₁ x)
    (hintype : ∀ a,(hincoming a).isRight=a.isRight)
    (houttype : ∀ x,(houtgoing x).isRight=x.isRight)
    (hAF : A₀∪A₁⊆F) (hXF : X₀∪X₁⊆F)
    (hsepA : ∀ z∈A₀∪A₁,¬PermutationClose π b z v)
    (hsepX : ∀ z∈X₀∪X₁,¬PermutationClose π b z v)
    (hY₀ : ∀ u∈Y₀,H₀ v u) (hY₁ : ∀ u∈Y₁,HK v u)
    (hbalA : A₀.card+A₁.card=Y₀.card+Y₁.card)
    (hbalX : X₀.card+X₁.card=Y₀.card+Y₁.card) (hmarked : A₁.card=Y₁.card)
    (K : ℕ) (hK : 0<K) (degree tau lam : ℝ) (htau : 0<tau) (hlam : 0<lam)
    (hcutloss : loss≤lam*tau)
    (hdeg : 2*tau+(2*(2*b+1):ℕ)≤degree) (hmargin : (2*(2*b+1):ℕ)<lam*tau)
    (hgap : (X₁.card:ℝ)+2*tau≤Y₀.card)
    (B₁ : BipartiteBlockBounds H₀ (fun a=>a∈A₁) (fun y=>y∈Y₁) (degree+loss) tau (2*lam))
    (B₂ : BipartiteBlockBounds H₀ (fun a=>a∈A₀) (fun y=>y∈Y₀) (degree+loss) tau (2*lam))
    (B₃ : BipartiteBlockBounds HK (fun a=>a∈X₁) (fun y=>y∈Y₀) (degree+loss) tau (2*lam))
    (B₄ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₀) (degree+loss) tau (2*lam))
    (B₅ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₁) (degree+loss) tau (2*lam))
    (hbudget : ((Fᶜ).card:ℝ)+((Y₀.card+Y₁.card)*(l+4):ℕ)/(K:ℝ)+
      (l+5)*(2*b+1)+8*(K+4:ℕ)+2*delta+2*dcol<c) :
    ∃ C : Fin (Y₀.card+Y₁.card) → MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i j,i≠j → Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      (∀ a,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (hincoming a))∈markedWheelPhysicalResources (C i)) ∧
      (∀ x,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (houtgoing x))∈markedWheelPhysicalResources (C i)) ∧
      (∀ u∈Y₀∪Y₁,∃ i,Sum.inr (v,u)∈markedWheelPhysicalResources (C i)) ∧
      (∀ x,(spanningRestriction (markedFamilyRim C) F).degree x≤4*(K+4)) ∧
      (∀ x∈F,(Finset.univ.filter (markedFamilySpokes C x)).card≤K+4) ∧
      (∀ w,(Finset.univ.filter (fun x=>markedFamilySpokes C x w)).card≤l+4) ∧
      (∀ i,markedWheelRows (C i)⊆insert v F) ∧
      (∀ i,(C i).2.val∈Y₀∪Y₁) ∧ (∀ i,v∈markedWheelRows (C i)) ∧
      (∀ i,Disjoint (markedWheelRimGraph (C i)) D) ∧
      (∀ x u,markedFamilySpokes C x u→¬J x u) := by
  let PE := fun e:E=>¬D.Adj (tail e) (head e)
  let PT := fun e:T=>¬D.Adj (ktail e) (π (khead e))
  have ha (a : A₀⊕A₁) : Sum.elim PE PT (hincoming a) :=
    marked_root_arc_survives_free_deletion tail head ktail khead π F hF D hDF v hv
      (hincoming a) (Or.inr (hinhead a))
  have hx (x : X₀⊕X₁) : Sum.elim PE PT (houtgoing x) :=
    marked_root_arc_survives_free_deletion tail head ktail khead π F hF D hDF v hv
      (houtgoing x) (Or.inl (houttail x))
  let ain := restrictedSumEmbedding hincoming PE PT ha
  let xout := restrictedSumEmbedding houtgoing PE PT hx
  have hJv (u : U) : ¬J v u := fun h=>hv (hJF v u h)
  have Q₁ := marked_host_extensions_after_rim_deletion Q D delta hdelta hD
  have Q₂ := marked_host_extensions_after_spoke_deletion Q₁ J drow dcol hJrow hJcol
  have hr (x : V) : ((Finset.univ.filter (J x)).card:ℝ)≤loss :=
    (by exact_mod_cast hJrow x : ((Finset.univ.filter (J x)).card:ℝ)≤drow).trans hrloss
  have hc (u : U) : ((Finset.univ.filter (fun x=>J x u)).card:ℝ)≤loss :=
    (by exact_mod_cast hJcol u : ((Finset.univ.filter (fun x=>J x u)).card:ℝ)≤dcol).trans hcloss
  obtain ⟨C,hC,hA,hX,hU,hR,hS,hCol,hrows,hhubs,hroots⟩ := marked_row_cover_on_labelled_parts Q₂ hl hb
    (markedRestrictedPhysical_injective PE PT hphys) F hF v hv A₀ A₁ X₀ X₁ Y₀ Y₁ hY ain xout
    (fun a=>(restrictedSumEmbedding_elim hincoming PE PT ha head khead a).trans (hinhead a))
    (fun a=>(restrictedSumEmbedding_elim hincoming PE PT ha tail ktail a).trans (hintail a))
    (fun x=>(restrictedSumEmbedding_elim houtgoing PE PT hx tail ktail x).trans (houttail x))
    (fun x=>(restrictedSumEmbedding_elim houtgoing PE PT hx head khead x).trans (houthead x))
    (fun a=>(restrictedSumEmbedding_type hincoming PE PT ha a).trans (hintype a))
    (fun x=>(restrictedSumEmbedding_type houtgoing PE PT hx x).trans (houttype x))
    hAF hXF hsepA hsepX (fun u hu=>⟨hY₀ u hu,hJv u⟩) (fun u hu=>⟨hY₁ u hu,hJv u⟩)
    hbalA hbalX hmarked K hK degree tau lam htau hlam hdeg hmargin hgap
    (bipartite_block_after_deletion H₀ J _ _ degree tau lam loss hlam.le B₁ hr hc hcutloss)
    (bipartite_block_after_deletion H₀ J _ _ degree tau lam loss hlam.le B₂ hr hc hcutloss)
    (bipartite_block_after_deletion HK J _ _ degree tau lam loss hlam.le B₃ hr hc hcutloss)
    (bipartite_block_after_deletion H₀ J _ _ degree tau lam loss hlam.le B₄ hr hc hcutloss)
    (bipartite_block_after_deletion H₀ J _ _ degree tau lam loss hlam.le B₅ hr hc hcutloss)
    (by linarith only [hbudget])
  let C' := fun i=>markedWheelToLarger PE PT (fun _ _ h=>h.1) (fun _ _ h=>h.1) (C i)
  have hres (i) : markedWheelPhysicalResources (C' i)=markedWheelPhysicalResources (C i) :=
    markedWheelToLarger_resources PE PT _ _ (C i)
  have hR' : markedFamilyRim C'=markedFamilyRim C := marked_restricted_family_rim PE PT _ _ C
  have hS' : markedFamilySpokes C'=markedFamilySpokes C := rfl
  refine ⟨C',?_,?_,?_,?_,?_,?_,?_,hrows,hhubs,hroots,?_,?_⟩
  · intro i j hij
    simpa only [hres] using hC i j hij
  · intro a
    obtain ⟨i,hi⟩ := hA a
    refine ⟨i,?_⟩
    rw [hres]
    have he := restrictedSumEmbedding_elim hincoming PE PT ha
      (fun e=>({tail e,head e}:Finset V)) (fun e=>({ktail e,π (khead e)}:Finset V)) a
    change Sum.inl (Sum.elim (fun e:{e//PE e}=>({tail e.val,head e.val}:Finset V))
      (fun e:{e//PT e}=>({ktail e.val,π (khead e.val)}:Finset V)) (restrictedSumEmbedding hincoming PE PT ha a))∈_ at hi
    rw [he] at hi
    exact hi
  · intro x
    obtain ⟨i,hi⟩ := hX x
    refine ⟨i,?_⟩
    rw [hres]
    have he := restrictedSumEmbedding_elim houtgoing PE PT hx
      (fun e=>({tail e,head e}:Finset V)) (fun e=>({ktail e,π (khead e)}:Finset V)) x
    change Sum.inl (Sum.elim (fun e:{e//PE e}=>({tail e.val,head e.val}:Finset V))
      (fun e:{e//PT e}=>({ktail e.val,π (khead e.val)}:Finset V)) (restrictedSumEmbedding houtgoing PE PT hx x))∈_ at hi
    rw [he] at hi
    exact hi
  · intro u hu
    obtain ⟨i,hi⟩ := hU u hu
    exact ⟨i,by simpa only [hres] using hi⟩
  · intro x
    have he := congrArg (fun G:SimpleGraph V=>(spanningRestriction G F).degree x) hR'
    exact he.le.trans (by convert hR x using 1 <;> congr!)
  · simpa only [hS'] using hS
  · simpa only [hS'] using hCol
  · intro i
    have he : markedWheelRimGraph (C' i)=markedWheelRimGraph (C i) := by
      unfold markedWheelRimGraph
      change physicalEdgeGraph (markedCyclePhysicalEdges _ _ _ _ _ _ _ (markedCycleToLarger PE PT (C i).1))=_
      rw [markedCycleToLarger_physical]
    rw [he]
    exact (marked_restricted_wheel_avoids_deletions D J (C i)).1
  · intro x u hu
    rw [hS'] at hu
    obtain ⟨i,hi,hx⟩ := hu
    exact (marked_restricted_wheel_avoids_deletions D J (C i)).2 x u
      ((markedWheelPhysicalResources_spoke (C i) x u).mpr ⟨hi,hx⟩)

end Oberwolfach
