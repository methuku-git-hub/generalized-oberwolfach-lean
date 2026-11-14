module

public import Oberwolfach.OrdinaryFiniteExpansion

@[expose] public section

/-! The injective maps of an expansion into a host, assembled from its
private labelled wheels. Old labels are fixed by the supplied embeddings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
variable {V₀ U₀ V U E J W : Type*}

def expansionRowEmbedding {I : Type*} (φ : V₀ ↪ V) (f : I → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v)
    (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b) : V₀ ⊕ (I×W) ↪ V where
  toFun := Sum.elim φ (fun p => f p.1 p.2)
  inj' := by
    intro a b he
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (φ.injective he)
      | inr p => exact False.elim (hroot p.1 p.2 a he.symm)
    | inr p =>
      cases b with
      | inl b => exact False.elim (hroot p.1 p.2 b he)
      | inr q =>
        rcases p with ⟨i,w⟩; rcases q with ⟨j,w'⟩
        have hij : i=j := by by_contra hh;exact hsep i j hh w w' he
        subst j
        exact congrArg (fun w => Sum.inr (i,w)) ((f i).injective he)

def expansionHubEmbedding {I : Type*} (ψ : U₀ ↪ U) (a : I → U)
    (hroot : ∀ i u,a i≠ψ u) (hsep : Function.Injective a) : U₀ ⊕ I ↪ U where
  toFun := Sum.elim ψ a
  inj' := by
    intro i j he
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (ψ.injective he)
      | inr j => exact False.elim (hroot j i he.symm)
    | inr i =>
      cases j with
      | inl j => exact False.elim (hroot i j he)
      | inr j => exact congrArg Sum.inr (hsep he)

@[simp] theorem expansionRowEmbedding_old (φ : V₀ ↪ V) (f : E⊕J → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v) (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b) (v : V₀) :
    expansionRowEmbedding φ f hroot hsep (.inl v)=φ v := rfl

@[simp] theorem expansionRowEmbedding_private (φ : V₀ ↪ V) (f : E⊕J → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v) (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b) (i : E⊕J) (w : W) :
    expansionRowEmbedding φ f hroot hsep (.inr (i,w))=f i w := rfl

@[simp] theorem expansionHubEmbedding_old (ψ : U₀ ↪ U) (a : E⊕J → U)
    (hroot : ∀ i u,a i≠ψ u) (hsep : Function.Injective a) (u : U₀) :
    expansionHubEmbedding ψ a hroot hsep (.inl u)=ψ u := rfl

@[simp] theorem expansionHubEmbedding_private (ψ : U₀ ↪ U) (a : E⊕J → U)
    (hroot : ∀ i u,a i≠ψ u) (hsep : Function.Injective a) (i : E⊕J) :
    expansionHubEmbedding ψ a hroot hsep (.inr i)=a i := rfl

theorem expansionRowEmbedding_hom (φ : V₀ ↪ V) (f : E⊕J → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v) (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b)
    (C : SimpleGraph W) (z o : W) (x y : E → V₀) (G : SimpleGraph V)
    (hcycle : ∀ i w w',C.Adj w w' → G.Adj (f i w) (f i w'))
    (hcross : ∀ e,G.Adj (φ (y e)) (f (.inl e) z) ∧ G.Adj (φ (x e)) (f (.inl e) o)) :
    ∀ a b,(ordinaryExpansionRim (J:=J) C z o x y).Adj a b →
      G.Adj (expansionRowEmbedding φ f hroot hsep a) (expansionRowEmbedding φ f hroot hsep b) := by
  have hcross' : ∀ v p,expansionCrossAdj z o x y v p → G.Adj (φ v) (f p.1 p.2) := by
    rintro v ⟨i,w⟩ h
    cases i with
    | inl e =>
      rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact (hcross e).2
      · exact (hcross e).1
    | inr j => exact False.elim h
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact False.elim h
    | inr p => exact hcross' a p h
  | inr p =>
    cases b with
    | inl b => exact (hcross' b p h).symm
    | inr q =>
      rcases p with ⟨i,w⟩;rcases q with ⟨j,w'⟩
      obtain ⟨rfl,hh⟩ := h
      cases i with
      | inl e => exact hcycle (.inl e) w w' hh.1
      | inr j => exact hcycle (.inr j) w w' hh

theorem expansionEmbedding_spokes (φ : V₀ ↪ V) (f : E⊕J → W ↪ V)
    (hroot : ∀ i w v,f i w≠φ v) (hsep : ∀ i j,i≠j → ∀ a b,f i a≠f j b)
    (ψ : U₀ ↪ U) (a : E⊕J → U) (huroot : ∀ i u,a i≠ψ u) (husep : Function.Injective a)
    (z : W) (v : J → V₀) (u : J → U₀) (H : V → U → Prop)
    (hH : ∀ i w,H (f i w) (a i))
    (hcross : ∀ j,H (φ (v j)) (a (.inr j)) ∧ H (f (.inr j) z) (ψ (u j))) :
    ∀ b c,ordinaryExpansionSpokes (E:=E) z v u b c →
      H (expansionRowEmbedding φ f hroot hsep b) (expansionHubEmbedding ψ a huroot husep c) := by
  intro b c h
  cases b with
  | inl b =>
    cases c with
    | inl c => exact False.elim h
    | inr i =>
      cases i with
      | inl e => exact False.elim h
      | inr j => subst b;exact (hcross j).1
  | inr p =>
    rcases p with ⟨i,w⟩
    cases i with
    | inl e =>
      cases c with
      | inl c => exact False.elim h
      | inr i => subst i;exact hH (.inl e) w
    | inr j =>
      cases c with
      | inl c => obtain ⟨rfl,rfl⟩ := h;exact (hcross j).2
      | inr i => obtain ⟨_,rfl⟩ := h;exact hH (.inr j) w

end Oberwolfach
