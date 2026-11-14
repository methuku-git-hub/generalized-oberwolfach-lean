module

public import Oberwolfach.OrdinaryExpansionHostFamily
public import Oberwolfach.OrdinaryExpansionEmbeddingMaps

@[expose] public section

/-! Actual embedding of the complete finite expansion. Every old label
is preserved, and every new label lies outside the prescribed old and
forbidden sets. This theorem assumes no wheel-embedding oracle. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_expansion_host_embedding (β : ℝ) (hβ : 0<β) (r q N : ℕ) (hr : 3≤r) :
    ∃ n₀ : ℕ,∀ n : ℕ,n₀≤n →
    ∀ (V₀ U₀ V U E J : Type*) [Fintype V] [Fintype U] [Fintype E] [Fintype J]
      [DecidableEq V] [DecidableEq U],Fintype.card V=n → Fintype.card (E⊕J)≤N →
    ∀ (G : SimpleGraph V) (H : V → U → Prop),
    (∀ a,(1/2+β)*(n:ℝ)≤G.degree a) →
    (∀ a,(1-1/(2*(r:ℝ)))*(Fintype.card U:ℝ)≤(Finset.univ.filter (H a)).card) →
    (∀ u,((Finset.univ.filter (fun v => ¬H v u)).card:ℝ)≤(β/2)*n) →
    (∀ u,((Finset.univ.filter (fun v => ¬H v u)).card:ℝ)≤(n:ℝ)/4) →
    ∀ (R : Finset V) (B : Finset U) (φ : V₀ ↪ V) (ψ : U₀ ↪ U)
      (x y : E → V₀) (v : J → V₀) (u : J → U₀),
      R.card≤q → (∀ a,φ a∈R) → (∀ b,ψ b∈B) → 2*(B.card+N)<Fintype.card U →
    ∃ (f : ExpansionRow V₀ E J (Fin r) ↪ V) (g : ExpansionHub U₀ E J ↪ U),
      (∀ a,f (.inl a)=φ a) ∧ (∀ b,g (.inl b)=ψ b) ∧
      (∀ i w,f (.inr (i,w))∉R) ∧ (∀ i,g (.inr i)∉B) ∧
      (∀ a b,(ordinaryExpansionRim (J:=J) (SimpleGraph.cycleGraph r)
        ⟨0,by omega⟩ ⟨r-1,by omega⟩ x y).Adj a b → G.Adj (f a) (f b)) ∧
      ∀ a b,ordinaryExpansionSpokes (E:=E) ⟨0,by omega⟩ v u a b → H (f a) (g b) := by
  obtain ⟨n₀,hfamily⟩ := ordinary_expansion_host_family β hβ r q N hr
  refine ⟨n₀,?_⟩
  intro n hn V₀ U₀ V U E J _ _ _ _ _ _ hV hN G H hdeg hrow hcol hquarter
    R B φ ψ x y v u hR hφ hψ hB
  obtain ⟨f,a,hf,hH,hfR,haB,hsep,hrim,hspoke⟩ := hfamily n hn V U E J hV hN G H
    hdeg hrow hcol hquarter R B (φ∘x) (φ∘y) (φ∘v) (ψ∘u) hR
    (fun e => ⟨hφ (x e),hφ (y e)⟩) (fun j => ⟨hφ (v j),hψ (u j)⟩) hB
  have hfroot : ∀ i w b,f i w≠φ b := by intro i w b he;exact hfR i w (he ▸ hφ b)
  have haroot : ∀ i b,a i≠ψ b := by intro i b he;exact haB i (he ▸ hψ b)
  have hainj : Function.Injective a := by intro i j he;by_contra hne;exact (hsep i j hne).1 he
  let f' := expansionRowEmbedding φ f hfroot (fun i j hij => (hsep i j hij).2)
  let g' := expansionHubEmbedding ψ a haroot hainj
  exact ⟨f',g',(fun _ => rfl),(fun _ => rfl),hfR,haB,
    expansionRowEmbedding_hom φ f hfroot (fun i j hij => (hsep i j hij).2)
      (SimpleGraph.cycleGraph r) ⟨0,by omega⟩ ⟨r-1,by omega⟩ x y G hf hrim,
    expansionEmbedding_spokes φ f hfroot (fun i j hij => (hsep i j hij).2)
      ψ a haroot hainj ⟨0,by omega⟩ v u H hH hspoke⟩

end Oberwolfach
