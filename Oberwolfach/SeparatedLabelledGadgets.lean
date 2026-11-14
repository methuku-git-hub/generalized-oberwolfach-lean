module

public import Oberwolfach.DisjointLabelledGadgets

@[expose] public section

/-! Successive private embeddings separated by an actual graph. All
previous rows are included before the next choice. The conclusion keeps
both inequality of labels and nonadjacency in the separation graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem separated_labelled_gadgets (r N : ℕ) (Fgraph : SimpleGraph V) (R : Finset V) (B : Finset U)
    (P : Fin N → (Fin r ↪ V) → U → Prop)
    (hlocal : ∀ i (S : Finset V) (T : Finset U),R⊆S → B⊆T →
      S.card≤R.card+N*r → T.card≤B.card+N →
      ∃ (f : Fin r ↪ V) (u : U),P i f u ∧ (∀ a,f a∉S) ∧ u∉T ∧ (∀ a z,z∈S → ¬Fgraph.Adj (f a) z)) :
    ∃ (f : Fin N → Fin r ↪ V) (u : Fin N → U),
      (∀ i,P i (f i) (u i) ∧ (∀ a,f i a∉R) ∧ u i∉B) ∧
      (∀ i j,i≠j → u i≠u j ∧ ∀ a b,f i a≠f j b ∧ ¬Fgraph.Adj (f i a) (f j b)) := by
  let allowed := fun i (o : Option ((Fin r ↪ V)×U)) =>
    ∃ f u,o=some (f,u) ∧ P i f u ∧ (∀ a,f a∉R) ∧ u∉B
  let compatible := fun (o p : Option ((Fin r ↪ V)×U)) =>
    ∀ f u g v,o=some (f,u) → p=some (g,v) → u≠v ∧ ∀ a b,f a≠g b ∧ ¬Fgraph.Adj (f a) (g b)
  obtain ⟨F,hF,hcomp⟩ := sequential_select_prefix N allowed compatible none (by
    intro i F _hprefix
    let J := Finset.univ.filter (fun j : Fin N => j.val < i.val)
    let S := R∪J.biUnion (fun j => optionLabelledRows (F j))
    let T := B∪J.biUnion (fun j => optionLabelledHubs (F j))
    have hJ : J.card≤N := (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)
    have hS : S.card≤R.card+N*r := by
      have hsum : (J.biUnion (fun j => optionLabelledRows (F j))).card≤J.card*r := by
        calc
          _ ≤ ∑ j∈J,(optionLabelledRows (F j)).card := Finset.card_biUnion_le
          _ ≤ ∑ _j∈J,r := Finset.sum_le_sum (fun _ _ => optionLabelledRows_card _)
          _ = _ := by simp
      have hh := Finset.card_union_le R (J.biUnion (fun j => optionLabelledRows (F j)))
      dsimp [S]
      nlinarith
    have hT : T.card≤B.card+N := by
      have hsum : (J.biUnion (fun j => optionLabelledHubs (F j))).card≤J.card := by
        calc
          _ ≤ ∑ j∈J,(optionLabelledHubs (F j)).card := Finset.card_biUnion_le
          _ ≤ ∑ _j∈J,1 := Finset.sum_le_sum (fun _ _ => optionLabelledHubs_card _)
          _ = _ := by simp
      have hh := Finset.card_union_le B (J.biUnion (fun j => optionLabelledHubs (F j)))
      dsimp [T]
      omega
    obtain ⟨f,u,hP,hf,hu,hFsep⟩ := hlocal i S T Finset.subset_union_left Finset.subset_union_left hS hT
    refine ⟨some (f,u),⟨f,u,rfl,hP,?_,?_⟩,?_⟩
    · exact fun a h => hf a (Finset.mem_union_left _ h)
    · exact fun h => hu (Finset.mem_union_left _ h)
    · intro j hj g v f' u' hg hfu
      have he : (f,u)=(f',u') := Option.some.inj hfu
      cases he
      have hjJ : j∈J := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
      refine ⟨?_,?_⟩
      · intro he
        apply hu
        apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨j,hjJ,?_⟩
        rw [hg]
        simpa [optionLabelledHubs] using he.symm
      · intro a b
        have haS : g a∈S := by
          apply Finset.mem_union_right
          apply Finset.mem_biUnion.mpr
          refine ⟨j,hjJ,?_⟩
          rw [hg]
          exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
        exact ⟨fun he => hf b (he ▸ haS),fun hadj => hFsep b (g a) haS hadj.symm⟩)
  choose f u he hP hf hu using hF
  refine ⟨f,u,(fun i => ⟨hP i,hf i,hu i⟩),?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h|h
  · exact hcomp i j h (f i) (u i) (f j) (u j) (he i) (he j)
  · have hh := hcomp j i h (f j) (u j) (f i) (u i) (he j) (he i)
    exact ⟨Ne.symm hh.1,fun a b => ⟨Ne.symm (hh.2 b a).1,fun he => (hh.2 b a).2 he.symm⟩⟩

theorem separated_labelled_gadgets_finite {I : Type*} [Fintype I]
    (r : ℕ) (Fgraph : SimpleGraph V) (R : Finset V) (B : Finset U) (P : I → (Fin r ↪ V) → U → Prop)
    (hlocal : ∀ i (S : Finset V) (T : Finset U),R⊆S → B⊆T →
      S.card≤R.card+Fintype.card I*r → T.card≤B.card+Fintype.card I →
      ∃ (f : Fin r ↪ V) (u : U),P i f u ∧ (∀ a,f a∉S) ∧ u∉T ∧ (∀ a z,z∈S → ¬Fgraph.Adj (f a) z)) :
    ∃ (f : I → Fin r ↪ V) (u : I → U),
      (∀ i,P i (f i) (u i) ∧ (∀ a,f i a∉R) ∧ u i∉B) ∧
      (∀ i j,i≠j → u i≠u j ∧ ∀ a b,f i a≠f j b ∧ ¬Fgraph.Adj (f i a) (f j b)) := by
  let e := Fintype.equivFin I
  obtain ⟨f,u,hP,hsep⟩ := separated_labelled_gadgets r (Fintype.card I) Fgraph R B
    (fun i => P (e.symm i)) (fun i => hlocal (e.symm i))
  refine ⟨fun i => f (e i),fun i => u (e i),?_,?_⟩
  · intro i
    simpa only [e.symm_apply_apply] using hP (e i)
  · intro i j hij
    exact hsep (e i) (e j) (fun he => hij (e.injective he))

end Oberwolfach
