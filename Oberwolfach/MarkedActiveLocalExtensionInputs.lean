module

public import Oberwolfach.MarkedInnerActiveNeighbourhoods
public import Oberwolfach.MarkedCoverDownExtensionInputs

@[expose] public section

/-! Apply the extension theorem after the actual two packings, retaining
all active roots and the original inner row and index error scales. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 8192
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_active_local_extension_inputs (c:ℕ) (alpha pstar omega:ℝ)
    (ha:0<alpha) (hp:0<pstar) (hp1:pstar≤1) (ho:0<omega):
    ∃ beta epsilon:ℝ,0<beta∧0<epsilon∧∀ d:ℕ,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (B:Finset U)
      (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (a:Γ) (j:Color) (errR errI:ℝ),
    N≤A.card→A.image π=A→pstar≤p→pstar≤k→
    (∀ u,pstar≤q u a)→(∀ u,pstar≤s u j)→
    omega*Fintype.card (V⊕U)≤(A.card:ℝ)→ omega*Fintype.card (V⊕U)≤(B.card:ℝ)→
    (∀ v,(1/2+alpha)*A.card≤((A∩P.neighborFinset v).card:ℝ))→
    errR≤epsilon*A.card→errI≤epsilon*B.card→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (c+6) A p k q s a j errR σ H→
    MarkedIndicesWithSpokes π d (c+6) B q s a j errI σ H→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1;let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1;let khead:=fun e:K=>e.val.2;
    MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) A (beta*Fintype.card (V⊕U))∧
    (∀ b x y u,x≠(if b then π y else y)→beta*Fintype.card (V⊕U)≤((A.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead b z y∧H false z u)).card:ℝ))∧
    (∀ e:E⊕K,¬PermutationClose π (3*d) (Sum.elim tail ktail e) (Sum.elim head khead e))∧
    (∀ e:E⊕K,beta*Fintype.card (V⊕U)≤((B.filter (fun u=>H false (Sum.elim tail ktail e) u∧
      (if markedArcType e then H true (Sum.elim head khead e) u else H false (Sum.elim head khead e) u))).card:ℝ)):=by
  obtain ⟨beta,epsilon,hb,he,hall⟩:=marked_cover_down_extension_inputs c alpha pstar omega ha hp hp1 ho
  refine ⟨beta,epsilon,hb,he,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hall d
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P π A B p k q s a j errR errI hn hA hp' hk' hq hs hAs hBs hdeg hR hI σ H hr hi
  exact hN V U Γ Color P π A B p k q s a j epsilon hn hA le_rfl hp' hk' hq hs hAs hBs hdeg σ H
    (fun S T J hS hT hJ hinj=>(hr S T J hS hT hJ hinj).trans_le hR)
    (fun J hJ hsep=>(hi J hJ hsep).trans_le hI)

end Oberwolfach
