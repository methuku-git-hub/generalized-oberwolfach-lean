module

public import Oberwolfach.ThreeBlockMatchingDeletion
public import Oberwolfach.PrescribedClassMatching
public import Oberwolfach.FiniteLabelConflicts

@[expose] public section

/-! Compatible marked endpoint assignments from the five actual degree/cut
blocks. The forbidden label relation is derived, not supplied as a matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_typed_endpoint_pairing_of_bounds
    {A X Y V : Type*} [Fintype A] [Fintype X] [Fintype Y] [Fintype V]
    (EA : A → Y → Prop) (EX : X → Y → Prop)
    (PA : A → Prop) (PX : X → Prop) (Q : Y → Prop)
    (hA : Fintype.card A=Fintype.card Y) (hX : Fintype.card X=Fintype.card Y)
    (hclass : Fintype.card {a // PA a}=Fintype.card {y // Q y})
    (hallowed : ∀ x y, EX x y → PX x → ¬Q y)
    (π : Equiv.Perm V) (b M : ℕ) (labelA : A → V) (labelX : X → V)
    (hfA : ∀ v, Fintype.card {a // labelA a=v}≤M)
    (hfX : ∀ v, Fintype.card {x // labelX x=v}≤M)
    (d a lam : ℝ) (ha : 0<a) (hlam : 0<lam)
    (hdegree : 2*a+(M*(2*b+1):ℕ)≤d)
    (hmargin : (M*(2*b+1):ℕ)<lam*a)
    (hgap : ((Finset.univ.filter PX).card:ℝ)+2*a≤(Finset.univ.filter (fun y => ¬Q y)).card)
    (B₁ : BipartiteBlockBounds EA PA Q d a lam)
    (B₂ : BipartiteBlockBounds EA (fun x => ¬PA x) (fun y => ¬Q y) d a lam)
    (B₃ : BipartiteBlockBounds EX PX (fun y => ¬Q y) d a lam)
    (B₄ : BipartiteBlockBounds EX (fun x => ¬PX x) (fun y => ¬Q y) d a lam)
    (B₅ : BipartiteBlockBounds EX (fun x => ¬PX x) Q d a lam) :
    ∃ f : A ≃ Y, ∃ g : X ≃ Y,
      (∀ x, EA x (f x)) ∧ (∀ x, EX x (g x)) ∧
      (∀ x, Q (f x) ↔ PA x) ∧ (∀ x, PX x → ¬Q (g x)) ∧
      ∀ y, ¬PermutationClose π b (labelA (f.symm y)) (labelX (g.symm y)) := by
  classical
  have hC : (0:ℝ)≤(M*(2*b+1):ℕ) := Nat.cast_nonneg _
  have hd : a≤d := by linarith
  obtain ⟨f₁,hf₁⟩ := bipartite_block_perfect_matching EA PA Q d a lam ha hd hlam B₁ hclass
  have hclass₀ : Fintype.card {x // ¬PA x}=Fintype.card {y // ¬Q y} := by
    rw [Fintype.card_subtype_compl,Fintype.card_subtype_compl,hA,hclass]
  obtain ⟨f₀,hf₀⟩ := bipartite_block_perfect_matching EA (fun x => ¬PA x)
    (fun y => ¬Q y) d a lam ha hd hlam B₂ (by convert hclass₀ using 1 <;> congr!)
  obtain ⟨f,hf,hftype⟩ := combine_class_matchings PA Q EA f₁ f₀ hf₁ hf₀
  let J (x : X) (y : Y) := PermutationClose π b (labelX x) (labelA (f.symm y))
  have hJrow (x : X) : ((Finset.univ.filter (J x)).card:ℝ)≤(M*(2*b+1):ℕ) := by
    have hh := label_permutation_close_card (fun y => labelA (f.symm y)) π b M
      (label_fibre_bound_reindex labelA f.symm M hfA) (labelX x)
    have hn : (Finset.univ.filter (J x)).card≤M*(2*b+1) := by
      simpa only [J,Fintype.card_subtype] using hh
    exact_mod_cast hn
  have hJcol (y : Y) : ((Finset.univ.filter (fun x => J x y)).card:ℝ)≤(M*(2*b+1):ℕ) := by
    have hh := label_permutation_close_card labelX π b M hfX (labelA (f.symm y))
    have he : (Finset.univ.filter (fun x => J x y))=
        Finset.univ.filter (fun x => PermutationClose π b (labelA (f.symm y)) (labelX x)) := by
      ext x; simp only [Finset.mem_filter,Finset.mem_univ,true_and,J]
      exact permutationClose_symm π b _ _
    rw [he]
    have hn : (Finset.univ.filter (fun x => PermutationClose π b (labelA (f.symm y)) (labelX x))).card≤M*(2*b+1) := by
      simpa only [Fintype.card_subtype] using hh
    exact_mod_cast hn
  obtain ⟨g,hg⟩ := three_block_matching_after_deletion EX J PX Q hX d a lam
    (M*(2*b+1):ℕ) ha hlam hdegree hmargin hgap B₃ B₄ B₅ hJrow hJcol
  refine ⟨f,g,hf,fun x => (hg x).1,hftype,fun x hx => hallowed x (g x) (hg x).1 hx,?_⟩
  intro y hclose
  have hh := (hg (g.symm y)).2
  apply hh
  dsimp [J]
  rw [g.apply_symm_apply]
  exact (permutationClose_symm π b _ _).mp hclose

end Oberwolfach
