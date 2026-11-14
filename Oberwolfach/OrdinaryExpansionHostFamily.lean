module

public import Oberwolfach.OrdinaryRimExpansionEmbedding
public import Oberwolfach.OrdinarySpokeExpansionEmbedding
public import Oberwolfach.DisjointLabelledGadgets

@[expose] public section

/-! All private wheels for a finite expansion are chosen simultaneously.
Formal rim pairs may repeat or be loops; formal spokes need not be host
edges. Only the cross-edges of their replacements are required and proved. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expansion_host_family (β : ℝ) (hβ : 0<β) (r q N : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V U E J : Type*) [Fintype V] [Fintype U] [Fintype E] [Fintype J]
      [DecidableEq V] [DecidableEq U],Fintype.card V=n → Fintype.card (E⊕J)≤N →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ a,(1/2+β)*(n:ℝ)≤G.degree a) →
    (∀ a,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card) →
    (∀ u,((Finset.univ.filter (fun v => ¬H v u)).card:ℝ)≤(β/2)*n) →
    (∀ u,((Finset.univ.filter (fun v => ¬H v u)).card:ℝ)≤(n:ℝ)/4) →
    ∀ (R : Finset V) (B : Finset U) (x y : E → V) (v : J → V) (u : J → U),
      R.card≤q → (∀ e,x e∈R ∧ y e∈R) → (∀ j,v j∈R ∧ u j∈B) →
      2*(B.card+N)<Fintype.card U →
    ∃ (f : E⊕J → Fin r ↪ V) (a : E⊕J → U),
      (∀ i j k,(SimpleGraph.cycleGraph r).Adj j k → G.Adj (f i j) (f i k)) ∧
      (∀ i j,H (f i j) (a i)) ∧ (∀ i j,f i j∉R) ∧ (∀ i,a i∉B) ∧
      (∀ i i',i≠i' → a i≠a i' ∧ ∀ j k,f i j≠f i' k) ∧
      (∀ e,G.Adj (y e) (f (.inl e) ⟨0,by omega⟩) ∧ G.Adj (x e) (f (.inl e) ⟨r-1,by omega⟩)) ∧
      ∀ j,H (v j) (a (.inr j)) ∧ H (f (.inr j) ⟨0,by omega⟩) (u j) := by
  obtain ⟨n₁,hrim⟩ := ordinary_rim_expansion_embedding β hβ r (q+N*r) hr
  obtain ⟨n₂,hspoke⟩ := ordinary_spoke_expansion_embedding β hβ r (q+N*r) hr
  refine ⟨max n₁ n₂,?_⟩
  intro n hn V U E J _ _ _ _ _ _ hV hN G H hdeg hrow hcol hquarter R B x y v u hR hxy hvu hB
  have hrow' : ∀ a,(1/2:ℝ)*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card := by
    intro a
    have hrR : (1:ℝ)≤r := by exact_mod_cast (show 1≤r by omega)
    have hfrac : 1/(2*(r:ℝ))≤1/2 := by apply (div_le_iff₀ (by positivity)).mpr;nlinarith
    have hh := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤1-1/(2*(r:ℝ)) by linarith)
      (Nat.cast_nonneg (Fintype.card U))
    exact hh.trans (hrow a)
  let P : E⊕J → (Fin r ↪ V) → U → Prop := fun i f a =>
    (∀ j k,(SimpleGraph.cycleGraph r).Adj j k → G.Adj (f j) (f k)) ∧
    (∀ j,H (f j) a) ∧
    Sum.elim (fun e => G.Adj (y e) (f ⟨0,by omega⟩) ∧ G.Adj (x e) (f ⟨r-1,by omega⟩))
      (fun j => H (v j) a ∧ H (f ⟨0,by omega⟩) (u j)) i
  obtain ⟨f,a,hf,hsep⟩ := disjoint_labelled_gadgets_finite r R B P (by
    intro i S T hRS hBT hS hT
    have hSq : S.card≤q+N*r := by nlinarith
    have hTb : 2*T.card<Fintype.card U := by omega
    cases i with
    | inl e =>
      obtain ⟨g,b,hg,hH,havoid,hb,hy,hx,_⟩ := hrim n ((le_max_left _ _).trans hn)
        V U hV.le G H hdeg hrow S T (x e) (y e) hSq (hRS (hxy e).1) (hRS (hxy e).2) hTb
      exact ⟨g,b,⟨hg,hH,hy,hx⟩,havoid,hb⟩
    | inr j =>
      obtain ⟨g,b,hg,hH,havoid,hb,hv,hu⟩ := hspoke n ((le_max_right _ _).trans hn)
        V U hV G H hdeg hrow' hcol hquarter S T (v j) (u j) hSq
        (hRS (hvu j).1) (hBT (hvu j).2) hTb
      exact ⟨g,b,⟨hg,hH,hv,hu⟩,havoid,hb⟩)
  exact ⟨f,a,(fun i => (hf i).1.1),(fun i => (hf i).1.2.1),
    (fun i => (hf i).2.1),(fun i => (hf i).2.2),hsep,
    (fun e => (hf (.inl e)).1.2.2),(fun j => (hf (.inr j)).1.2.2)⟩

end Oberwolfach
