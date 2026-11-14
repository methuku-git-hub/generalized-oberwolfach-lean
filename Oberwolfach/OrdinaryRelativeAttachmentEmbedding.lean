module

public import Oberwolfach.OrdinaryRelativeAttachmentRoot
public import Oberwolfach.OrdinaryAttachmentEmbeddingMaps
public import Oberwolfach.SeparatedLabelledGadgets

@[expose] public section

/-! The full attachment embedding in a relative host, preserving the old
subgraph and every prescribed root. Its private rows and hubs are chosen
by the proved local constructions, with separation retained globally. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U I : Type} [Fintype V] [Fintype U] [Fintype I]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_relative_attachment_embedding (Q F : SimpleGraph V) (H : V → U → Prop)
    (A W R : Finset V) (B : Finset U) (φ : V₀ ↪ V) (ψ : U₀ ↪ U)
    (G₀ : SimpleGraph V₀) (H₀ : V₀ → U₀ → Prop) (ρ : I → V₀)
    (hφ : ∀ a,φ a∈R) (hψ : ∀ b,ψ b∈B)
    (hG₀ : ∀ a b,G₀.Adj a b → Q.Adj (φ a) (φ b)) (hH₀ : ∀ a b,H₀ a b → H (φ a) (ψ b))
    (r : ℕ) (hr : 3≤r) (d c cH : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub : ∀ T:Finset V,T.card≤r → (∀ v∈T,∀ w∈T,¬F.Adj v w) →
      cH≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+Fintype.card I*r+r+6)*(d+1)<c)
    (hB : (B.card:ℝ)+Fintype.card I<cH) :
    ∃ (f : V₀⊕(I×Fin r) ↪ V) (g : U₀⊕I ↪ U),
      (∀ a,f (.inl a)=φ a) ∧ (∀ b,g (.inl b)=ψ b) ∧
      (∀ i w,f (.inr (i,w))∈A ∧ f (.inr (i,w))∉W ∧ f (.inr (i,w))∉R ∧
        ∀ z∈R,¬F.Adj (f (.inr (i,w))) z) ∧
      (∀ i,g (.inr i)∉B) ∧
      (∀ i j w w',¬F.Adj (f (.inr (i,w))) (f (.inr (j,w')))) ∧
      (∀ a b,(ordinaryAttachmentRim G₀ (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ρ).Adj a b → Q.Adj (f a) (f b)) ∧
      ∀ a b,ordinaryAttachmentSpokes H₀ ⟨0,by omega⟩ ρ a b → H (f a) (g b) := by
  let z : Fin r := ⟨0,by omega⟩
  let C := SimpleGraph.cycleGraph r
  let P : I → (Fin r ↪ V) → U → Prop := fun i f a =>
    (∀ j k,j≠z → k≠z → C.Adj j k → Q.Adj (f j) (f k)) ∧
    (∀ j,C.Adj z j → Q.Adj (φ (ρ i)) (f j)) ∧ H (φ (ρ i)) a ∧ (∀ j,j≠z → H (f j) a) ∧
    (∀ j k,¬F.Adj (f j) (f k)) ∧
    ∀ j,f j∈A ∧ f j∉W ∧ f j∉R ∧ ∀ v∈R,¬F.Adj (f j) v
  obtain ⟨f,a,hf,hsep⟩ := separated_labelled_gadgets_finite r F R B P (by
    intro i S T hRS hBT hS hT
    have hSc : (S.card:ℝ)≤R.card+Fintype.card I*r := by exact_mod_cast hS
    have hTc : (T.card:ℝ)≤B.card+Fintype.card I := by exact_mod_cast hT
    obtain ⟨f,a,hC,hcross,hrootH,hH,ha,hind,havoid⟩ := ordinary_relative_attachment_root Q F H A W S T
      (φ (ρ i)) (hRS (hφ (ρ i))) r hr d c cH hd hF hcount
      (by nlinarith only [hbudget,hSc,hd]) hhub (hTc.trans_lt hB)
    refine ⟨f,a,⟨hC,hcross,hrootH,hH,hind,?_⟩,(fun j => (havoid j).2.2.1),ha,?_⟩
    · intro j
      exact ⟨(havoid j).1,(havoid j).2.1,(fun h => (havoid j).2.2.1 (hRS h)),
        fun v hv => (havoid j).2.2.2 v (hRS hv)⟩
    · intro j v hv
      exact (havoid j).2.2.2 v hv)
  have hfroot : ∀ i w b,f i w≠φ b := by intro i w b he;exact (hf i).2.1 w (he ▸ hφ b)
  have haroot : ∀ i b,a i≠ψ b := by intro i b he;exact (hf i).2.2 (he ▸ hψ b)
  have hainj : Function.Injective a := by intro i j he;by_contra hne;exact (hsep i j hne).1 he
  have hfsep : ∀ i j,i≠j → ∀ w w',f i w≠f j w' := fun i j hij w w' => ((hsep i j hij).2 w w').1
  let f' := expansionRowEmbedding φ f hfroot hfsep
  let g' := expansionHubEmbedding ψ a haroot hainj
  refine ⟨f',g',(fun _ => rfl),(fun _ => rfl),(fun i => (hf i).1.2.2.2.2.2),(fun i => (hf i).2.2),?_,
    attachmentRowEmbedding_hom φ f hfroot hfsep G₀ C z ρ Q hG₀ (fun i => (hf i).1.1) (fun i => (hf i).1.2.1),
    attachmentEmbedding_spokes φ f hfroot hfsep ψ a haroot hainj H₀ z ρ H hH₀
      (fun i => (hf i).1.2.2.2.1) (fun i => (hf i).1.2.2.1)⟩
  intro i j w w'
  by_cases hij : i=j
  · subst j;exact (hf i).1.2.2.2.2.1 w w'
  · exact ((hsep i j hij).2 w w').2

end Oberwolfach
