module

public import Oberwolfach.OrdinaryAttachmentRootEmbedding
public import Oberwolfach.OrdinaryExpansionEmbeddingMaps
public import Oberwolfach.OrdinaryFiniteAttachments
public import Oberwolfach.DisjointLabelledGadgets

@[expose] public section

/-! Embed every attached wheel with separate private vertices and hubs.
Repeated prescribed roots are allowed. The old graph and spokes are
retained, and the unused private zero labels are also embedded injectively. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_attachment_host_embedding (β : ℝ) (hβ : 0<β) (r q N : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V₀ U₀ V U I : Type*) [Fintype V] [Fintype U] [Fintype I]
      [DecidableEq V] [DecidableEq U],Fintype.card V=n → Fintype.card I≤N →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ a,(1/2+β)*(n:ℝ)≤G.degree a) →
    (∀ a,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card) →
    ∀ (R : Finset V) (B : Finset U) (φ : V₀ ↪ V) (ψ : U₀ ↪ U)
      (G₀ : SimpleGraph V₀) (H₀ : V₀ → U₀ → Prop) (ρ : I → V₀),
      R.card≤q → (∀ a,φ a∈R) → (∀ b,ψ b∈B) → 2*(B.card+N)<Fintype.card U →
      (∀ a b,G₀.Adj a b → G.Adj (φ a) (φ b)) → (∀ a b,H₀ a b → H (φ a) (ψ b)) →
    ∃ (f : V₀ ⊕ (I×Fin r) ↪ V) (g : U₀⊕I ↪ U),
      (∀ a,f (.inl a)=φ a) ∧ (∀ b,g (.inl b)=ψ b) ∧
      (∀ i w,f (.inr (i,w))∉R) ∧ (∀ i,g (.inr i)∉B) ∧
      (∀ a b,(ordinaryAttachmentRim G₀ (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).Adj a b → G.Adj (f a) (f b)) ∧
      ∀ a b,ordinaryAttachmentSpokes H₀ ⟨0,by omega⟩ ρ a b → H (f a) (g b) := by
  obtain ⟨n₀,hroot⟩ := ordinary_attachment_root_embedding β hβ r (q+N*r) hr
  refine ⟨n₀,?_⟩
  intro n hn V₀ U₀ V U I _ _ _ _ _ hV hN G H hdeg hrow R B φ ψ G₀ H₀ ρ hR hφ hψ hB hG₀ hH₀
  let z : Fin r := ⟨0,by omega⟩
  let C := SimpleGraph.cycleGraph r
  let P : I → (Fin r ↪ V) → U → Prop := fun i f a =>
    (∀ j k,j≠z → k≠z → C.Adj j k → G.Adj (f j) (f k)) ∧
    (∀ j,C.Adj z j → G.Adj (φ (ρ i)) (f j)) ∧ H (φ (ρ i)) a ∧ ∀ j,j≠z → H (f j) a
  obtain ⟨f,a,hf,hsep⟩ := disjoint_labelled_gadgets_finite r R B P (by
    intro i S T hRS hBT hS hT
    have hSq : S.card≤q+N*r := by nlinarith
    have hTb : 2*T.card<Fintype.card U := by omega
    obtain ⟨f,a,hC,hcross,hrootH,hH,havoid,ha⟩ := hroot n hn V U hV G H hdeg hrow S T
      (φ (ρ i)) hSq (hRS (hφ (ρ i))) hTb
    exact ⟨f,a,⟨hC,hcross,hrootH,hH⟩,havoid,ha⟩)
  have hfroot : ∀ i w b,f i w≠φ b := by intro i w b he;exact (hf i).2.1 w (he ▸ hφ b)
  have haroot : ∀ i b,a i≠ψ b := by intro i b he;exact (hf i).2.2 (he ▸ hψ b)
  have hainj : Function.Injective a := by intro i j he;by_contra hne;exact (hsep i j hne).1 he
  let f' := expansionRowEmbedding φ f hfroot (fun i j hij => (hsep i j hij).2)
  let g' := expansionHubEmbedding ψ a haroot hainj
  refine ⟨f',g',(fun _ => rfl),(fun _ => rfl),(fun i => (hf i).2.1),(fun i => (hf i).2.2),?_,?_⟩
  · intro b c h
    cases b with
    | inl b =>
      cases c with
      | inl c => exact hG₀ b c h
      | inr p =>
        rcases p with ⟨i,w⟩
        change ρ i=b ∧ w≠z ∧ C.Adj z w at h
        rcases h with ⟨rfl,_,hc⟩
        exact (hf i).1.2.1 w hc
    | inr p =>
      rcases p with ⟨i,w⟩
      cases c with
      | inl c =>
        change ρ i=c ∧ w≠z ∧ C.Adj z w at h
        rcases h with ⟨rfl,_,hc⟩
        exact ((hf i).1.2.1 w hc).symm
      | inr p =>
        rcases p with ⟨j,w'⟩
        change i=j ∧ w≠z ∧ w'≠z ∧ C.Adj w w' at h
        obtain ⟨rfl,hw,hw',hc⟩ := h
        exact (hf i).1.1 w w' hw hw' hc
  · intro b c h
    cases b with
    | inl b =>
      cases c with
      | inl c => exact hH₀ b c h
      | inr i =>
        change ρ i=b at h
        subst b
        exact (hf i).1.2.2.1
    | inr p =>
      rcases p with ⟨i,w⟩
      cases c with
      | inl c => exact False.elim h
      | inr j =>
        change w≠z ∧ i=j at h
        obtain ⟨hw,rfl⟩ := h
        exact (hf i).1.2.2.2 w hw

end Oberwolfach
