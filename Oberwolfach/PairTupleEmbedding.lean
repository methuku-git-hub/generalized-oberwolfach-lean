module

public import Oberwolfach.EmbeddedWeights

@[expose] public section

/-! Transport from labelled class vertices to actual vertex tuples.
Injectivity proves that the same tuple weight is retained, and the
incidence formulas retain the specified coordinate positions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def pairTupleEmbedding {I X V : Type*} (f g : I → X ↪ V) :
    (I → X × X) ↪ (I → V × V) where
  toFun s i := (f i (s i).1, g i (s i).2)
  inj' := by
    intro s t h
    funext i
    exact Prod.ext ((f i).injective (congrArg Prod.fst (congrFun h i)))
      ((g i).injective (congrArg Prod.snd (congrFun h i)))

theorem pairTupleEmbedding_range {I X V : Type*} (f g : I → X ↪ V) (t : I → V × V) :
    t ∈ Set.range (pairTupleEmbedding f g) ↔
      ∀ i, (t i).1 ∈ Set.range (f i) ∧ (t i).2 ∈ Set.range (g i) := by
  constructor
  · rintro ⟨s,rfl⟩ i
    exact ⟨⟨(s i).1,rfl⟩,⟨(s i).2,rfl⟩⟩
  · intro h
    choose a ha using fun i => (h i).1
    choose b hb using fun i => (h i).2
    refine ⟨fun i => (a i,b i), ?_⟩
    funext i
    exact Prod.ext (ha i) (hb i)

theorem pairTuple_weight_left_edge {I X V : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Fintype V]
    (f g : I → X ↪ V) (w : (I → X × X) → ℝ) (i : I) (x y : X) :
    (∑ t, if t i = (f i x,g i y) then embeddedWeight (pairTupleEmbedding f g) w t else 0) =
      ∑ s, if s i = (x,y) then w s else 0 := by
  have h := embeddedWeight_incidence (pairTupleEmbedding f g) w
    (fun t => t i = (f i x,g i y))
  convert h using 1
  · apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro s _
    have he : pairTupleEmbedding f g s i = (f i x,g i y) ↔ s i = (x,y) := by
      change (f i (s i).1,g i (s i).2) = (f i x,g i y) ↔ _
      rw [Prod.mk.injEq, (f i).injective.eq_iff, (g i).injective.eq_iff]
      constructor
      · rintro ⟨h₁,h₂⟩; exact Prod.ext h₁ h₂
      · intro h; exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    simp only [he]

theorem pairTuple_weight_cross_edge {I X V : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Fintype V]
    (f g : I → X ↪ V) (w : (I → X × X) → ℝ) (i j : I) (y z : X) :
    (∑ t, if ((t i).2,(t j).1) = (g i y,f j z)
      then embeddedWeight (pairTupleEmbedding f g) w t else 0) =
      ∑ s, if ((s i).2,(s j).1) = (y,z) then w s else 0 := by
  have h := embeddedWeight_incidence (pairTupleEmbedding f g) w
    (fun t => ((t i).2,(t j).1) = (g i y,f j z))
  convert h using 1
  · apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> rfl
  · apply Finset.sum_congr rfl
    intro s _
    simp only [pairTupleEmbedding, Function.Embedding.coeFn_mk, Prod.mk.injEq,
      (f j).injective.eq_iff, (g i).injective.eq_iff]

theorem pairTuple_weight_positions {I X V : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Fintype V]
    (f g : I → X ↪ V) (w : (I → X × X) → ℝ) (i : I) (x : X) :
    (∑ t, if (t i).1 = f i x then embeddedWeight (pairTupleEmbedding f g) w t else 0) =
      (∑ s, if (s i).1 = x then w s else 0) ∧
    (∑ t, if (t i).2 = g i x then embeddedWeight (pairTupleEmbedding f g) w t else 0) =
      (∑ s, if (s i).2 = x then w s else 0) := by
  constructor
  · have h := embeddedWeight_incidence (pairTupleEmbedding f g) w (fun t => (t i).1 = f i x)
    simpa only [pairTupleEmbedding, Function.Embedding.coeFn_mk, (f i).injective.eq_iff] using h
  · have h := embeddedWeight_incidence (pairTupleEmbedding f g) w (fun t => (t i).2 = g i x)
    simpa only [pairTupleEmbedding, Function.Embedding.coeFn_mk, (g i).injective.eq_iff] using h

theorem pairTuple_weight_position_outside {I X V : Type*}
    [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X] [Fintype V]
    (f g : I → X ↪ V) (w : (I → X × X) → ℝ) (i : I) (v : V)
    (hv : v ∉ Set.range (f i)) :
    (∑ t, if (t i).1 = v then embeddedWeight (pairTupleEmbedding f g) w t else 0) = 0 := by
  rw [embeddedWeight_incidence]
  apply Finset.sum_eq_zero
  intro s _
  exact if_neg (fun h => hv ⟨(s i).1,h⟩)

end Oberwolfach
