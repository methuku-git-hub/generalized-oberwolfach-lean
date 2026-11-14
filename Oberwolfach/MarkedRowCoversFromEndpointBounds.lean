module

public import Oberwolfach.MarkedRowCoverAfterFreeDeletion
public import Oberwolfach.MarkedSequentialRowCover
public import Oberwolfach.MarkedComparisonCover
public import Oberwolfach.MarkedRowRequiredResources

@[expose] public section

/-! Successive marked row covers from actual endpoint blocks. Every
one-row existence premise of the induction is discharged by the proved
bounded-deletion construction; the root stars and coefficient choices
remain fixed throughout. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T : Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head : E→V} {ktail khead : T→V} {H₀ HK : V→U→Prop}
    {π : Equiv.Perm V} {b l n : ℕ} {c ch : ℝ}

theorem marked_row_covers_from_endpoint_bounds
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (hb : 1≤b) (hphys : Function.Injective (markedPhysicalEdge tail head ktail khead π))
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
      (l+5)*(2*b+1)+8*(K+4:ℕ)+2*(n*(4*(K+4)):ℕ)+2*(n*(l+4):ℕ)<c) :
    ∃ C : Fin n→Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      (∀ i,MarkedRowCover (C i) (v i) F
        (markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
          (π:=π) (ain i) (xout i) (v i) (Y₀ i∪Y₁ i)) (Y₀ i∪Y₁ i) K) ∧
      (∀ i j,i≠j→Disjoint ((C i).biUnion markedWheelPhysicalResources)
        ((C j).biUnion markedWheelPhysicalResources)) := by
  let required := fun i=>markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
    (π:=π) (ain i) (xout i) (v i) (Y₀ i∪Y₁ i)
  apply sequential_marked_row_covers v hv F hvF required (fun i=>Y₀ i∪Y₁ i)
  intro i M havoid hMr hMs hMc
  let D := spanningRestriction (markedPackingRimGraph M) F
  let J := fun x u=>x∈F ∧ markedPackingSpokes M x u
  have hD (x : V) : (D.degree x:ℝ)≤(n*(4*(K+4)):ℕ) := by exact_mod_cast hMr x
  have hJrow (x : V) : (Finset.univ.filter (J x)).card≤n*(K+4) := by
    by_cases hx : x∈F
    · simpa only [J,hx,true_and] using hMs x hx
    · simp [J,hx]
  have hJcol (u : U) : (Finset.univ.filter (fun x=>J x u)).card≤n*(l+4) := by
    apply (Finset.card_le_card (show Finset.univ.filter (fun x=>J x u)⊆
      Finset.univ.filter (fun x=>markedPackingSpokes M x u) from
        fun x hx=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2.2⟩)).trans
    simpa only [Nat.add_assoc] using hMc u
  obtain ⟨W,hW,hA,hX,hU,hR,hS,hCol,hrows,hhubs,hroots,hWD,hWJ⟩ :=
    marked_row_cover_after_free_deletion Q hl hb hphys F hF (v i) (hvF i)
      D (fun x y h=>(spanningRestriction_adj _ _ _ _).mp h |>.2)
      J (fun x u h=>h.1) (n*(4*(K+4)):ℕ) (by positivity) hD
      (n*(K+4)) (n*(l+4)) (by convert hJrow using 1 <;> congr!)
      (by convert hJcol using 1 <;> congr!) loss hrloss hcloss
      (A₀ i) (A₁ i) (X₀ i) (X₁ i) (Y₀ i) (Y₁ i) (hY i) (ain i) (xout i)
      (hinhead i) (hintail i) (houttail i) (houthead i) (hintype i) (houttype i)
      (hAF i) (hXF i) (hsepA i) (hsepX i) (hY₀ i) (hY₁ i)
      (hbalA i) (hbalX i) (hmarked i) K hK degree tau lam htau hlam hcutloss hdeg hmargin (hgap i)
      (B₁ i) (B₂ i) (B₃ i) (B₄ i) (B₅ i) (hbudget i)
  let N := Finset.univ.image W
  have hN : MarkedRowCover N (v i) F (required i) (Y₀ i∪Y₁ i) K :=
    markedRowCover_of_family W (v i) F (required i) (Y₀ i∪Y₁ i) K hW hrows hhubs hroots
      (marked_row_required_covered (ain i) (xout i) (v i) (Y₀ i∪Y₁ i)
        (fun j=>markedWheelPhysicalResources (W j)) hA hX hU) hR hS (by simpa only [Nat.add_assoc] using hCol)
  refine ⟨N,hN,?_⟩
  apply marked_comparison_cover_disjoint (by omega) hb hphys M N F hF (v i) havoid hN.rows
  · intro Z hZ
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hZ
    exact hWD j
  · intro x u hu
    have he : markedPackingSpokes N=markedFamilySpokes W := marked_family_image_spokes W
    rw [he] at hu
    exact hWJ x u hu

end Oberwolfach
