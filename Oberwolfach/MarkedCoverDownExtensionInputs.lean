module

public import Oberwolfach.MarkedSampleExtensionCounts

@[expose] public section

/-! Fixed-domain row and index estimates imply all extension inputs of the
active cover-down theorem. The coefficient and the tolerance are chosen
before the separation distance and the actual marginal arrays. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 14000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_cover_down_extension_inputs (c:ℕ) (α pstar omega:ℝ)
    (hα:0<α) (hpstar:0<pstar) (hpstar1:pstar≤1) (homega:0<omega):
    ∃ β ε₀:ℝ,0<β∧0<ε₀∧∀ d:ℕ,∃ N:ℕ,
    ∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [LinearOrder V] [DecidableEq U],
    ∀ (P:SimpleGraph V) (π:Equiv.Perm V) (A:Finset V) (B:Finset U)
      (p k:ℝ) (q:U→Γ→ℝ) (s:U→Color→ℝ) (g:Γ) (j:Color) (ε:ℝ),
    N≤A.card→A.image π=A→ε≤ε₀→pstar≤p→pstar≤k→
    (∀ u,pstar≤q u g)→(∀ u,pstar≤s u j)→
    omega*Fintype.card (V⊕U)≤(A.card:ℝ)→ omega*Fintype.card (V⊕U)≤(B.card:ℝ)→
    (∀ v,(1/2+α)*A.card≤((A∩P.neighborFinset v).card:ℝ))→
    ∀ (σ:RawMarkedOutcome V U Γ Color) (H:Bool→V→U→Prop),
    MarkedRowsWithSpokes P π d (c+6) A p k q s g j (ε*A.card) σ H→
    MarkedIndicesWithSpokes π d (c+6) B q s g j (ε*B.card) σ H→
    let E:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) false
    let K:=MarkedSampleArc P π (3*d) (fun e=>σ (Sum.inl e)) true
    let tail:=fun e:E=>e.val.1; let head:=fun e:E=>e.val.2
    let ktail:=fun e:K=>e.val.1; let khead:=fun e:K=>e.val.2;
    MarkedBoundaryExtensionCounts tail head ktail khead (H false) (H true) A (β*Fintype.card (V⊕U)) ∧
    (∀ b x y u,x≠(if b then π y else y)→β*Fintype.card (V⊕U)≤((A.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead b z y∧H false z u)).card:ℝ)) ∧
    (∀ e:E⊕K,¬PermutationClose π (3*d) (Sum.elim tail ktail e) (Sum.elim head khead e)) ∧
    (∀ e:E⊕K,β*Fintype.card (V⊕U)≤((B.filter (fun u=>H false (Sum.elim tail ktail e) u∧
      (if markedArcType e then H true (Sum.elim head khead e) u else
        H false (Sum.elim head khead e) u))).card:ℝ)):=by
  obtain ⟨β₀,ε₀,hβ₀,hε₀,hlocal⟩:=marked_common_event_local_extensions c α pstar hα hpstar hpstar1
  refine ⟨β₀*omega,ε₀,mul_pos hβ₀ homega,hε₀,?_⟩
  intro d
  obtain ⟨N,hN⟩:=hlocal d
  refine ⟨N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ P π A B p k q s g j ε hn hA he hp hk hq hs hAsize hBsize hdeg σ H hr hi
  obtain ⟨hstep,hjoin,hcommon⟩:=hN V U Γ Color P π A B p k q s g j ε
    hn hA he hp hk hq hs hdeg σ H hr hi
  have hAlow:(β₀*omega)*Fintype.card (V⊕U)≤β₀*A.card:=by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hAsize hβ₀.le
  have hBlow:(β₀*omega)*Fintype.card (V⊕U)≤β₀*B.card:=by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hBsize hβ₀.le
  exact marked_sample_extension_counts P π d (c+6) (by omega) A B σ H
    ((β₀*omega)*Fintype.card (V⊕U)) ((β₀*omega)*Fintype.card (V⊕U))
    (fun b x u=>hAlow.trans (hstep b x u))
    (fun b x y u hxy=>hAlow.trans (hjoin b x y u hxy))
    (fun X Y hXY hsize hsep=>hBlow.trans (hcommon X Y hXY hsize hsep))

end Oberwolfach
