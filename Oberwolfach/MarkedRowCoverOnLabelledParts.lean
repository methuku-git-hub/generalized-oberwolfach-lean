module

public import Oberwolfach.MarkedRowCoverFromEndpointBounds
public import Oberwolfach.TaggedSubsetEmbedding

@[expose] public section

/-! Assemble the five literal endpoint blocks into a row cover. All arc
indices are retained, and their label fibre bound is proved from the two
type classes. The root degree and marked degree equalities are explicit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {b l : ℕ} {c ch : ℝ}

theorem marked_row_cover_on_labelled_parts
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (hb : 1≤b) (hphys : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F) (v : V) (hv : v∉F)
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
    (hdeg : 2*tau+(2*(2*b+1):ℕ)≤degree) (hmargin : (2*(2*b+1):ℕ)<lam*tau)
    (hgap : (X₁.card:ℝ)+2*tau≤Y₀.card)
    (B₁ : BipartiteBlockBounds H₀ (fun a=>a∈A₁) (fun y=>y∈Y₁) degree tau lam)
    (B₂ : BipartiteBlockBounds H₀ (fun a=>a∈A₀) (fun y=>y∈Y₀) degree tau lam)
    (B₃ : BipartiteBlockBounds HK (fun a=>a∈X₁) (fun y=>y∈Y₀) degree tau lam)
    (B₄ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₀) degree tau lam)
    (B₅ : BipartiteBlockBounds H₀ (fun a=>a∈X₀) (fun y=>y∈Y₁) degree tau lam)
    (hbudget : ((Fᶜ).card:ℝ)+((Y₀.card+Y₁.card)*(l+4):ℕ)/(K:ℝ)+
      (l+5)*(2*b+1)+8*(K+4:ℕ)<c) :
    ∃ C : Fin (Y₀.card+Y₁.card) → MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i j,i≠j → Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j))) ∧
      (∀ a,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (hincoming a))∈markedWheelPhysicalResources (C i)) ∧
      (∀ x,∃ i,Sum.inl (markedPhysicalEdge tail head ktail khead π (houtgoing x))∈markedWheelPhysicalResources (C i)) ∧
      (∀ u∈Y₀∪Y₁,∃ i,Sum.inr (v,u)∈markedWheelPhysicalResources (C i)) ∧
      (∀ x,(spanningRestriction (markedFamilyRim C) F).degree x≤4*(K+4)) ∧
      (∀ x∈F,(Finset.univ.filter (markedFamilySpokes C x)).card≤K+4) ∧
      (∀ w,(Finset.univ.filter (fun x=>markedFamilySpokes C x w)).card≤l+4) ∧
      (∀ i,markedWheelRows (C i)⊆insert v F) ∧
      (∀ i,(C i).2.val∈Y₀∪Y₁) ∧ (∀ i,v∈markedWheelRows (C i)) := by
  let hub := taggedSubsetEmbedding Y₀ Y₁ hY
  have hinlabel (a : A₀⊕A₁) : taggedSubsetValue A₀ A₁ a∈A₀∪A₁ := by
    cases a with
    | inl a=>exact Finset.mem_union_left _ a.property
    | inr a=>exact Finset.mem_union_right _ a.property
  have houtlabel (x : X₀⊕X₁) : taggedSubsetValue X₀ X₁ x∈X₀∪X₁ := by
    cases x with
    | inl x=>exact Finset.mem_union_left _ x.property
    | inr x=>exact Finset.mem_union_right _ x.property
  have hhub (y : Y₀⊕Y₁) : if y.isRight then HK v (hub y) else H₀ v (hub y) := by
    cases y with
    | inl y=>exact hY₀ y.val y.property
    | inr y=>exact hY₁ y.val y.property
  have hclass : Fintype.card {a : A₀⊕A₁ // (hincoming a).isRight=true}=
      Fintype.card {y : Y₀⊕Y₁ // y.isRight=true} := by
    simp only [hintype,Fintype.card_subtype,tagged_right_card,hmarked]
  obtain ⟨D₁,D₂,D₃,D₄,D₅⟩ := marked_endpoint_assignment_blocks A₀ A₁ X₀ X₁ Y₀ Y₁ H₀ HK
    degree tau lam B₁ B₂ B₃ B₄ B₅
  obtain ⟨C,hC,hA,hX,hU,hR,hS,hCol,hrows,hhubs,hroots⟩ := marked_row_cover_from_endpoint_bounds Q hl hb hphys F hF v hv
    (Y₀.card+Y₁.card) K 2 hK hincoming houtgoing hub Sum.isRight
    (by simpa using hbalA) (by simpa using hbalX) (by simp)
    hinhead houttail (fun a=>by rw [hintail];exact hAF (hinlabel a))
    (fun x=>by rw [houthead];exact hXF (houtlabel x))
    (fun a=>by rw [hintail];exact hsepA _ (hinlabel a))
    (fun x=>by rw [houthead];exact hsepX _ (houtlabel x)) hhub
    (by
      intro z
      simp only [hintail]
      convert tagged_subset_label_fibre A₀ A₁ z using 1 <;> congr!)
    (by
      intro z
      simp only [houthead]
      convert tagged_subset_label_fibre X₀ X₁ z using 1 <;> congr!)
    (markedIncomingAssignment A₀ A₁ Y₀ Y₁ H₀) (markedOutgoingAssignment X₀ X₁ Y₀ Y₁ H₀ HK)
    (by intro a y ha;rw [hintail];exact ha.2)
    (by intro x y hx;rw [houthead,houttype];exact hx.2)
    (by intro x y hx ht;exact fun hy=>hx.1 ⟨by simpa only [houttype] using ht,hy⟩)
    hclass degree tau lam htau hlam hdeg hmargin
    (by simpa only [houttype,tagged_right_card,tagged_left_card] using hgap)
    (by simpa only [hintype] using D₁) (by simpa only [hintype] using D₂)
    (by simpa only [houttype] using D₃) (by simpa only [houttype] using D₄)
    (by simpa only [houttype] using D₅) (by simpa using hbudget)
  refine ⟨C,hC,hA,hX,?_,hR,hS,hCol,hrows,?_,hroots⟩
  · intro u hu
    rcases Finset.mem_union.mp hu with hu|hu
    · exact hU (Sum.inl ⟨u,hu⟩)
    · exact hU (Sum.inr ⟨u,hu⟩)
  · intro i
    obtain ⟨y,hy⟩ := hhubs i
    rw [hy]
    cases y with
    | inl y=>exact Finset.mem_union_left _ y.property
    | inr y=>exact Finset.mem_union_right _ y.property

end Oberwolfach
