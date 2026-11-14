module

public import Oberwolfach.BipartiteBlockMatching

@[expose] public section

/-! Transport block estimates through actual bijections of the selected
parts. Labels outside a fixed type class are not identified. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem bipartite_block_transport
    {X Y A B : Type} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (E : X→Y→Prop) (E' : A→B→Prop)
    (P : X→Prop) (Q : Y→Prop) (P' : A→Prop) (Q' : B→Prop)
    (f : {x // P' x} ≃ {x // P x}) (g : {y // Q' y} ≃ {y // Q y})
    (he : ∀ x y,E' x.val y.val ↔ E (f x).val (g y).val)
    (d tau lam : ℝ) (H : BipartiteBlockBounds E P Q d tau lam) :
    BipartiteBlockBounds E' P' Q' d tau lam := by
  classical
  have hrow (x : {a // P' a}) :
      (Finset.univ.filter (fun y=>Q' y ∧ E' x.val y)).card=
        (Finset.univ.filter (fun y=>Q y ∧ E (f x).val y)).card := by
    apply Finset.card_bij (fun y hy=>(g ⟨y,(Finset.mem_filter.mp hy).2.1⟩).val)
    · intro y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(g _).property,(he x _).mp (Finset.mem_filter.mp hy).2.2⟩
    · intro y hy z hz heq
      exact congrArg Subtype.val (g.injective (Subtype.ext heq))
    · intro y hy
      let z := g.symm ⟨y,(Finset.mem_filter.mp hy).2.1⟩
      have hz : E' x.val z.val := by
        apply (he x z).mpr
        simpa only [z,g.apply_symm_apply] using (Finset.mem_filter.mp hy).2.2
      refine ⟨z.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.property,hz⟩,?_⟩
      exact congrArg Subtype.val (g.apply_symm_apply ⟨y,(Finset.mem_filter.mp hy).2.1⟩)
  have hcol (y : {b // Q' b}) :
      (Finset.univ.filter (fun x=>P' x ∧ E' x y.val)).card=
        (Finset.univ.filter (fun x=>P x ∧ E x (g y).val)).card := by
    apply Finset.card_bij (fun x hx=>(f ⟨x,(Finset.mem_filter.mp hx).2.1⟩).val)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(f _).property,(he _ y).mp (Finset.mem_filter.mp hx).2.2⟩
    · intro x hx z hz heq
      exact congrArg Subtype.val (f.injective (Subtype.ext heq))
    · intro x hx
      let z := f.symm ⟨x,(Finset.mem_filter.mp hx).2.1⟩
      have hz : E' z.val y.val := by
        apply (he z y).mpr
        simpa only [z,f.apply_symm_apply] using (Finset.mem_filter.mp hx).2.2
      refine ⟨z.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,z.property,hz⟩,?_⟩
      exact congrArg Subtype.val (f.apply_symm_apply ⟨x,(Finset.mem_filter.mp hx).2.1⟩)
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rw [hrow ⟨x,hx⟩]
    exact H.row _ (f _).property
  · intro y hy
    rw [hcol ⟨y,hy⟩]
    exact H.col _ (g _).property
  · intro S T hS hT hs ht
    let fs : S→X := fun x=>(f ⟨x.val,hS x.val x.property⟩).val
    let gt : T→Y := fun y=>(g ⟨y.val,hT y.val y.property⟩).val
    have hfs : Function.Injective fs := by
      intro x z hz
      exact Subtype.ext (congrArg (fun a : {x // P' x}=>a.val) (f.injective (Subtype.ext hz)))
    have hgt : Function.Injective gt := by
      intro x z hz
      exact Subtype.ext (congrArg (fun b : {y // Q' y}=>b.val) (g.injective (Subtype.ext hz)))
    let S' := Finset.univ.image fs
    let T' := Finset.univ.image gt
    have hSc : S'.card=S.card := by simp [S',Finset.card_image_of_injective _ hfs]
    have hTc : T'.card=T.card := by simp [T',Finset.card_image_of_injective _ hgt]
    have hp : ∀ x∈S',P x := by
      intro x hx;obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hx;exact (f _).property
    have hq : ∀ y∈T',Q y := by
      intro y hy;obtain ⟨z,hz,rfl⟩:=Finset.mem_image.mp hy;exact (g _).property
    have hc := H.cut S' T' hp hq (by simpa only [hSc] using hs) (by simpa only [hTc] using ht)
    have hcut : (bipartiteMatrixCut (fun x y=>if E x y then 1 else 0) S' T':ℝ)=
        bipartiteMatrixCut (fun x y=>if E' x y then 1 else 0) S T := by
      unfold bipartiteMatrixCut
      dsimp only [S',T']
      rw [Finset.sum_image hfs.injOn]
      simp_rw [Finset.sum_image hgt.injOn]
      have hc' : (∑ x : S,∑ y : T,if E (fs x) (gt y) then (1:ℕ) else 0)=
          ∑ x : S,∑ y : T,if E' x.val y.val then (1:ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        simp only [fs,gt,←he]
      rw [hc']
      apply congrArg (fun n : ℕ=>(n:ℝ))
      trans ∑ x : S,∑ y∈T,if E' x.val y then (1:ℕ) else 0
      · apply Finset.sum_congr rfl
        intro x hx
        convert Finset.sum_coe_sort T (fun y=>if E' x.val y then (1:ℕ) else 0) using 1 <;> congr!
      · convert Finset.sum_coe_sort S (fun x=>∑ y∈T,if E' x y then (1:ℕ) else 0) using 1 <;> congr!

    rw [hSc,hTc,hcut] at hc
    exact hc

end Oberwolfach
