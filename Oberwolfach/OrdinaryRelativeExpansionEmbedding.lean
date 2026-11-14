module

public import Oberwolfach.OrdinaryRelativeExpansionFamily
public import Oberwolfach.OrdinaryExpansionEmbeddingMaps

@[expose] public section

/-! Embed the whole finite expansion into the relative host. All private
rows are separated from each other and from every prescribed old row;
formal loops and repeated pairs remain permitted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V₀ U₀ V U E J : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype J]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_relative_expansion_embedding (Q F : SimpleGraph V) (H : V → U → Prop)
    (A W R : Finset V) (B : Finset U) (φ : V₀ ↪ V) (ψ : U₀ ↪ U)
    (x y : E → V₀) (v : J → V₀) (u : J → U₀)
    (hφ : ∀ a,φ a∈R) (hψ : ∀ b,ψ b∈B)
    (r : ℕ) (hr : 3≤r) (d c cH : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair : ∀ u u' v w,c≤(((A.filter (fun a => H a u ∧ H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub : ∀ T:Finset V,T.card≤r → (∀ v∈T,∀ w∈T,¬F.Adj v w) →
      cH≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+Fintype.card (E⊕J)*r+r+6)*(d+1)<c)
    (hB : (B.card:ℝ)+Fintype.card (E⊕J)<cH) :
    ∃ (f : ExpansionRow V₀ E J (Fin r) ↪ V) (g : ExpansionHub U₀ E J ↪ U),
      (∀ a,f (.inl a)=φ a) ∧ (∀ b,g (.inl b)=ψ b) ∧
      (∀ i w,f (.inr (i,w))∈A ∧ f (.inr (i,w))∉W ∧ f (.inr (i,w))∉R ∧
        ∀ z∈R,¬F.Adj (f (.inr (i,w))) z) ∧
      (∀ i,g (.inr i)∉B) ∧
      (∀ i j w w',¬F.Adj (f (.inr (i,w))) (f (.inr (j,w')))) ∧
      (∀ a b,(ordinaryExpansionRim (J:=J) (SimpleGraph.cycleGraph r)
        ⟨0,by omega⟩ ⟨r-1,by omega⟩ x y).Adj a b → Q.Adj (f a) (f b)) ∧
      ∀ a b,ordinaryExpansionSpokes (E:=E) ⟨0,by omega⟩ v u a b → H (f a) (g b) := by
  obtain ⟨f,a,hf,hH,hfR,haB,hind,hsep,hrim,hspoke⟩ := ordinary_relative_expansion_family Q F H A W R B
    (φ∘x) (φ∘y) (φ∘v) (ψ∘u) r hr d c cH hd hF hcount hpair hhub hbudget hB
  have hfroot : ∀ i w b,f i w≠φ b := by intro i w b he;exact (hfR i w).2.2.1 (he ▸ hφ b)
  have haroot : ∀ i b,a i≠ψ b := by intro i b he;exact haB i (he ▸ hψ b)
  have hainj : Function.Injective a := by intro i j he;by_contra hne;exact (hsep i j hne).1 he
  have hfsep : ∀ i j,i≠j → ∀ w w',f i w≠f j w' := fun i j hij w w' => ((hsep i j hij).2 w w').1
  let f' := expansionRowEmbedding φ f hfroot hfsep
  let g' := expansionHubEmbedding ψ a haroot hainj
  refine ⟨f',g',(fun _ => rfl),(fun _ => rfl),hfR,haB,?_,
    expansionRowEmbedding_hom φ f hfroot hfsep (SimpleGraph.cycleGraph r)
      ⟨0,by omega⟩ ⟨r-1,by omega⟩ x y Q hf hrim,
    expansionEmbedding_spokes φ f hfroot hfsep ψ a haroot hainj ⟨0,by omega⟩ v u H hH hspoke⟩
  intro i j w w'
  by_cases hij : i=j
  · subst j;exact hind i w w'
  · exact ((hsep i j hij).2 w w').2

end Oberwolfach
