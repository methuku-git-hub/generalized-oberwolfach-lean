module

public import Oberwolfach.DenseBipartitePerfectMatching

@[expose] public section

/-! Two applications of Hall produce a triangle factor in a balanced
tripartite graph whose three bipartite graphs have minimum degree at least
three quarters of a part. No regularity or fractional weights are required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem large_sets_half_intersection {V : Type*} [Fintype V] [DecidableEq V]
    (A B : Finset V) (hA : 3*Fintype.card V≤4*A.card) (hB : 3*Fintype.card V≤4*B.card) :
    Fintype.card V≤2*(A∩B).card := by
  have hh := Finset.card_union_add_card_inter A B
  have hU := Finset.card_le_univ (A∪B)
  omega

theorem tripartite_triangle_bijections {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (E₀₁ : X→Y→Prop) (E₀₂ : X→Z→Prop) (E₁₂ : Y→Z→Prop)
    (hXY : Fintype.card X=Fintype.card Y) (hXZ : Fintype.card X=Fintype.card Z)
    (h₀₁r : ∀ x,3*Fintype.card Y≤4*(Finset.univ.filter (E₀₁ x)).card)
    (h₀₁c : ∀ y,3*Fintype.card X≤4*(Finset.univ.filter (fun x=>E₀₁ x y)).card)
    (h₀₂r : ∀ x,3*Fintype.card Z≤4*(Finset.univ.filter (E₀₂ x)).card)
    (h₀₂c : ∀ z,3*Fintype.card X≤4*(Finset.univ.filter (fun x=>E₀₂ x z)).card)
    (h₁₂r : ∀ y,3*Fintype.card Z≤4*(Finset.univ.filter (E₁₂ y)).card)
    (h₁₂c : ∀ z,3*Fintype.card Y≤4*(Finset.univ.filter (fun y=>E₁₂ y z)).card) :
    ∃ σ : X≃Y,∃ τ : X≃Z,∀ x,E₀₁ x (σ x) ∧ E₀₂ x (τ x) ∧ E₁₂ (σ x) (τ x) := by
  classical
  obtain ⟨σ,hσ⟩ := dense_bipartite_perfect_matching E₀₁ hXY
    (fun x=>by have hh:=h₀₁r x;omega) (fun y=>by have hh:=h₀₁c y;omega)
  let E : X→Z→Prop := fun x z=>E₀₂ x z ∧ E₁₂ (σ x) z
  have hrow (x : X) : Fintype.card Z≤2*(Finset.univ.filter (E x)).card := by
    have he : Finset.univ.filter (E x)=(Finset.univ.filter (E₀₂ x))∩(Finset.univ.filter (E₁₂ (σ x))) := by
      ext z;simp [E]
    rw [he]
    exact large_sets_half_intersection _ _ (h₀₂r x) (h₁₂r (σ x))
  have hcol (z : Z) : Fintype.card X≤2*(Finset.univ.filter (fun x=>E x z)).card := by
    have hcard : (Finset.univ.filter (fun x=>E₁₂ (σ x) z)).card=
        (Finset.univ.filter (fun y=>E₁₂ y z)).card := by
      apply Finset.card_bij (fun x _=>σ x)
      · intro x hx;simpa using hx
      · intro x _ y _ h;exact σ.injective h
      · intro y hy;exact ⟨σ.symm y,by simpa using hy,σ.apply_symm_apply y⟩
    have he : Finset.univ.filter (fun x=>E x z)=
        (Finset.univ.filter (fun x=>E₀₂ x z))∩(Finset.univ.filter (fun x=>E₁₂ (σ x) z)) := by
      ext x;simp [E]
    rw [he]
    apply large_sets_half_intersection _ _ (h₀₂c z)
    rw [hcard,hXY]
    exact h₁₂c z
  obtain ⟨τ,hτ⟩ := dense_bipartite_perfect_matching E hXZ (fun x=>by convert hrow x using 1 <;> congr!) (fun z=>by convert hcol z using 1 <;> congr!)
  exact ⟨σ,τ,fun x=>⟨hσ x,hτ x⟩⟩

end Oberwolfach
