module

public import Oberwolfach.MarkedRowCoversFromEndpointBounds
public import Oberwolfach.MarkedRowCoverRestrictionLift
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

theorem marked_row_covers_after_initial_rim_deletion
    (Q : MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl : 2≤l) (hb : 1≤b) (hphys : Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (F : Finset V) (hF : ∀ z,π z∈F ↔ z∈F)
    (D : SimpleGraph V) (hDF : GraphSupportedOn F D)
    (delta : ℝ) (hdelta : 0≤delta) (hD : ∀ x,(D.degree x:ℝ)≤delta)
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
      (l+5)*(2*b+1)+8*(K+4:ℕ)+2*(n*(4*(K+4)):ℕ)+2*(n*(l+4):ℕ)+2*delta<c) :
    ∃ C : Fin n→Finset (MarkedWheel tail head ktail khead (l+3) π b H₀ HK),
      (∀ i,MarkedRowCover (C i) (v i) F
        (markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead)
          (π:=π) (ain i) (xout i) (v i) (Y₀ i∪Y₁ i)) (Y₀ i∪Y₁ i) K) ∧
      (∀ i j,i≠j→Disjoint ((C i).biUnion markedWheelPhysicalResources)
        ((C j).biUnion markedWheelPhysicalResources)) ∧
      (∀ i,Disjoint (markedPackingRimGraph (C i)) D) := by
  let PE := fun e:E=>¬D.Adj (tail e) (head e)
  let PT := fun e:T=>¬D.Adj (ktail e) (π (khead e))
  have ha (i) (a : A₀ i⊕A₁ i) : Sum.elim PE PT (ain i a) :=
    marked_root_arc_survives_free_deletion tail head ktail khead π F hF D hDF (v i) (hvF i)
      (ain i a) (Or.inr (hinhead i a))
  have hx (i) (x : X₀ i⊕X₁ i) : Sum.elim PE PT (xout i x) :=
    marked_root_arc_survives_free_deletion tail head ktail khead π F hF D hDF (v i) (hvF i)
      (xout i x) (Or.inl (houttail i x))
  let ain' := fun i=>restrictedSumEmbedding (ain i) PE PT (ha i)
  let xout' := fun i=>restrictedSumEmbedding (xout i) PE PT (hx i)
  have Q' := marked_host_extensions_after_rim_deletion Q D delta hdelta hD
  obtain ⟨C,hC,hcross⟩ := marked_row_covers_from_endpoint_bounds Q' hl hb
    (markedRestrictedPhysical_injective PE PT hphys) F hF v hv hvF A₀ A₁ X₀ X₁ Y₀ Y₁ hY ain' xout'
    (fun i a=>(restrictedSumEmbedding_elim (ain i) PE PT (ha i) head khead a).trans (hinhead i a))
    (fun i a=>(restrictedSumEmbedding_elim (ain i) PE PT (ha i) tail ktail a).trans (hintail i a))
    (fun i x=>(restrictedSumEmbedding_elim (xout i) PE PT (hx i) tail ktail x).trans (houttail i x))
    (fun i x=>(restrictedSumEmbedding_elim (xout i) PE PT (hx i) head khead x).trans (houthead i x))
    (fun i a=>(restrictedSumEmbedding_type (ain i) PE PT (ha i) a).trans (hintype i a))
    (fun i x=>(restrictedSumEmbedding_type (xout i) PE PT (hx i) x).trans (houttype i x))
    hAF hXF hsepA hsepX hY₀ hY₁ hbalA hbalX hmarked K hK degree tau lam htau hlam hdeg hmargin hgap
    loss hrloss hcloss hcutloss B₁ B₂ B₃ B₄ B₅ (by intro i;linarith only [hbudget i])
  let lift := markedWheelToLarger (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (m:=l+3) (π:=π) (b:=b) PE PT
    (fun (x:V) (u:U) (h:H₀ x u)=>h) (fun (x:V) (u:U) (h:HK x u)=>h)
  let C' := fun i=>(C i).image lift
  have he (i) : (C' i).biUnion markedWheelPhysicalResources=(C i).biUnion markedWheelPhysicalResources :=
    markedWheelToLarger_cover PE PT _ _ (C i)
  refine ⟨C',?_,?_,?_⟩
  · intro i
    have hh := marked_row_cover_lift PE PT (fun _ _ h=>h) (fun _ _ h=>h) (C i)
      (v i) F _ (Y₀ i∪Y₁ i) K (hC i)
    have hreq : markedRowRequiredResources (tail:=fun e:{e//PE e}=>tail e.val) (head:=fun e=>head e.val)
        (ktail:=fun e:{e//PT e}=>ktail e.val) (khead:=fun e=>khead e.val) (π:=π)
        (ain' i) (xout' i) (v i) (Y₀ i∪Y₁ i)=
      markedRowRequiredResources (tail:=tail) (head:=head) (ktail:=ktail) (khead:=khead) (π:=π)
        (ain i) (xout i) (v i) (Y₀ i∪Y₁ i) := by
      have hfa : (fun a=>Sum.inl (β:=V×U) (markedPhysicalEdge
          (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
          (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) π (ain' i a)))=
          (fun a=>Sum.inl (β:=V×U) (markedPhysicalEdge tail head ktail khead π (ain i a))) := by
        funext a
        exact congrArg Sum.inl (restrictedSumEmbedding_elim (ain i) PE PT (ha i)
          (fun e=>({tail e,head e}:Finset V)) (fun e=>({ktail e,π (khead e)}:Finset V)) a)
      have hfx : (fun x=>Sum.inl (β:=V×U) (markedPhysicalEdge
          (fun e:{e//PE e}=>tail e.val) (fun e=>head e.val)
          (fun e:{e//PT e}=>ktail e.val) (fun e=>khead e.val) π (xout' i x)))=
          (fun x=>Sum.inl (β:=V×U) (markedPhysicalEdge tail head ktail khead π (xout i x))) := by
        funext x
        exact congrArg Sum.inl (restrictedSumEmbedding_elim (xout i) PE PT (hx i)
          (fun e=>({tail e,head e}:Finset V)) (fun e=>({ktail e,π (khead e)}:Finset V)) x)
      unfold markedRowRequiredResources
      rw [hfa,hfx]
    rw [hreq] at hh
    exact hh
  · intro i j hij
    simpa only [he] using hcross i j hij
  · intro i
    apply disjoint_iff_inf_le.mpr
    intro x y hxy
    rw [marked_packing_lift_rim] at hxy
    obtain ⟨W,hW,hw⟩ := Finset.mem_biUnion.mp hxy.1.2
    exact (marked_cycle_rim_avoids_deleted_graph D W.1 x y hw hxy.2).elim

end Oberwolfach
