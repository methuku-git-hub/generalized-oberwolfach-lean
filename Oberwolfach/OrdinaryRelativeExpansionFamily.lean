module

public import Oberwolfach.OrdinarySparseExpansionHubs
public import Oberwolfach.SeparatedLabelledGadgets

@[expose] public section

/-! Simultaneous expansion embeddings under the actual common-neighbour
hypotheses. New labels are mutually separated and separated from all old
row labels; the old labels need not be separated from each other. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E J : Type} [Fintype V] [Fintype U] [Fintype E] [Fintype J]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_relative_expansion_family (Q F : SimpleGraph V) (H : V → U → Prop)
    (A W R : Finset V) (B : Finset U) (x y : E → V) (v : J → V) (u : J → U)
    (r : ℕ) (hr : 3≤r) (d c cH : ℝ) (hd : 0≤d)
    (hF : ∀ v,(F.degree v:ℝ)≤d)
    (hcount : ∀ v w,c≤((A∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hpair : ∀ u u' v w,c≤(((A.filter (fun a => H a u ∧ H a u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ))
    (hhub : ∀ T:Finset V,T.card≤r → (∀ v∈T,∀ w∈T,¬F.Adj v w) →
      cH≤((common Finset.univ T (fun v => Finset.univ.filter (H v))).card:ℝ))
    (hbudget : W.card+((R.card:ℝ)+Fintype.card (E⊕J)*r+r+6)*(d+1)<c)
    (hB : (B.card:ℝ)+Fintype.card (E⊕J)<cH) :
    ∃ (f : E⊕J → Fin r ↪ V) (a : E⊕J → U),
      (∀ i j k,(SimpleGraph.cycleGraph r).Adj j k → Q.Adj (f i j) (f i k)) ∧
      (∀ i j,H (f i j) (a i)) ∧
      (∀ i j,f i j∈A ∧ f i j∉W ∧ f i j∉R ∧ ∀ z∈R,¬F.Adj (f i j) z) ∧
      (∀ i,a i∉B) ∧ (∀ i j k,¬F.Adj (f i j) (f i k)) ∧
      (∀ i i',i≠i' → a i≠a i' ∧ ∀ j k,f i j≠f i' k ∧ ¬F.Adj (f i j) (f i' k)) ∧
      (∀ e,Q.Adj (y e) (f (.inl e) ⟨0,by omega⟩) ∧ Q.Adj (x e) (f (.inl e) ⟨r-1,by omega⟩)) ∧
      ∀ j,H (v j) (a (.inr j)) ∧ H (f (.inr j) ⟨0,by omega⟩) (u j) := by
  let P : E⊕J → (Fin r ↪ V) → U → Prop := fun i f a =>
    (∀ j k,(SimpleGraph.cycleGraph r).Adj j k → Q.Adj (f j) (f k)) ∧
    (∀ j,H (f j) a) ∧ (∀ j k,¬F.Adj (f j) (f k)) ∧
    (∀ j,f j∈A ∧ f j∉W ∧ f j∉R ∧ ∀ z∈R,¬F.Adj (f j) z) ∧
    Sum.elim (fun e => Q.Adj (y e) (f ⟨0,by omega⟩) ∧ Q.Adj (x e) (f ⟨r-1,by omega⟩))
      (fun j => H (v j) a ∧ H (f ⟨0,by omega⟩) (u j)) i
  obtain ⟨f,a,hf,hsep⟩ := separated_labelled_gadgets_finite r F R B P (by
    intro i S T hRS hBT hS hT
    have hSc : (S.card:ℝ)≤R.card+Fintype.card (E⊕J)*r := by exact_mod_cast hS
    have hTc : (T.card:ℝ)≤B.card+Fintype.card (E⊕J) := by exact_mod_cast hT
    have hSc' : W.card+((S.card:ℝ)+r+6)*(d+1)<c := by nlinarith only [hSc,hbudget,hd]
    have hTc' : (T.card:ℝ)<cH := hTc.trans_lt hB
    cases i with
    | inl e =>
      obtain ⟨g,b,hg,hH,hb,hy,hx,hind,havoid⟩ := sparse_rim_expansion_embedding Q F H A W S T
        (x e) (y e) r hr d c cH hd hF hcount hSc' hhub hTc'
      refine ⟨g,b,⟨hg,hH,hind,?_,hy,hx⟩,(fun j => (havoid j).2.2.1),hb,?_⟩
      · intro j
        exact ⟨(havoid j).1,(havoid j).2.1,(fun h => (havoid j).2.2.1 (hRS h)),
          fun z hz => (havoid j).2.2.2 z (hRS hz)⟩
      · intro j z hz
        exact (havoid j).2.2.2 z hz
    | inr j =>
      obtain ⟨g,b,hg,hH,hb,hv,hu,hind,havoid⟩ := sparse_spoke_expansion_embedding Q F H A W S T
        (v j) (u j) r hr d c cH hd hF hpair hSc' hhub hTc'
      refine ⟨g,b,⟨hg,hH,hind,?_,hv,hu⟩,(fun k => (havoid k).2.2.1),hb,?_⟩
      · intro k
        exact ⟨(havoid k).1,(havoid k).2.1,(fun h => (havoid k).2.2.1 (hRS h)),
          fun z hz => (havoid k).2.2.2 z (hRS hz)⟩
      · intro k z hz
        exact (havoid k).2.2.2 z hz)
  exact ⟨f,a,(fun i => (hf i).1.1),(fun i => (hf i).1.2.1),
    (fun i => (hf i).1.2.2.2.1),(fun i => (hf i).2.2),
    (fun i => (hf i).1.2.2.1),hsep,
    (fun e => (hf (.inl e)).1.2.2.2.2),(fun j => (hf (.inr j)).1.2.2.2.2)⟩

end Oberwolfach
