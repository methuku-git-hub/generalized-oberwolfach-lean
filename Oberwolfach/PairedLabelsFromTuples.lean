module

public import Oberwolfach.PairedAbsorberRecords
public import Oberwolfach.DisjointTupleChoices

@[expose] public section

/-! Explicit recovery of every root, base label and common-path label
from a paired absorber record. The map does not identify orderings. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

def pairedTupleLabels (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V) :
    Fin ((m+1)*(m+1)) ⊕ Fin (m+1) → V
  | Sum.inl p => let ij := finProdFinEquiv.symm p; Fin.cons (α:=fun _ => V) (y ij.1) (g ij.1) ij.2
  | Sum.inr i => x i

theorem pairedTupleLabels_free (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V)
    (i j : Fin (m+1)) : pairedTupleLabels x y g (pairedFreePosition i j)=Fin.cons (α:=fun _ => V) (y i) (g i) j := by
  simp only [pairedTupleLabels,pairedFreePosition,Equiv.symm_apply_apply]

theorem pairedTupleLabels_root (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V)
    (i : Fin (m+1)) : pairedTupleLabels x y g (pairedRootPosition i)=x i := rfl

theorem pairedTupleLabels_injective (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxy : ∀ i j,y i≠x j)
    (havoid : ∀ i j,g i j∉Finset.univ.image x∪Finset.univ.image y)
    (hg : Function.Injective (fun p : Fin (m+1)×Fin m => g p.1 p.2)) :
    Function.Injective (pairedTupleLabels x y g) := by
  have hrow : Function.Injective (fun p : Fin (m+1)×Fin (m+1) => Fin.cons (α:=fun _ => V) (y p.1) (g p.1) p.2) := by
    rintro ⟨i,j⟩ ⟨i',j'⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · refine Fin.cases ?_ (fun j' => ?_) j'
      · intro he
        exact Prod.ext (hy he) rfl
      · intro he
        exact False.elim (havoid i' j' (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i,Finset.mem_univ _,by simpa only [Fin.cons_zero,Fin.cons_succ] using he⟩)))
    · refine Fin.cases ?_ (fun j' => ?_) j'
      · intro he
        exact False.elim (havoid i j (Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨i',Finset.mem_univ _,by simpa only [Fin.cons_zero,Fin.cons_succ] using he.symm⟩)))
      · intro he
        have hh := hg (a₁:=(i,j)) (a₂:=(i',j')) (by simpa only [Fin.cons_succ] using he)
        cases hh
        rfl
  have hfree (p : Fin ((m+1)*(m+1))) (j : Fin (m+1)) : pairedTupleLabels x y g (Sum.inl p)≠x j := by
    let ij := finProdFinEquiv.symm p
    change Fin.cons (α:=fun _ => V) (y ij.1) (g ij.1) ij.2≠x j
    refine Fin.cases ?_ (fun l => ?_) ij.2
    · exact hxy ij.1 j
    · intro he
      exact havoid ij.1 l (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,he.symm⟩))
  intro p q he
  rcases p with p|p <;> rcases q with q|q
  · apply congrArg Sum.inl
    apply finProdFinEquiv.symm.injective
    exact hrow he
  · exact (hfree p q he).elim
  · exact (hfree q p he.symm).elim
  · exact congrArg Sum.inr (hx he)

theorem pairedTupleLabels_base (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V) :
    (pairedBasePositions (c:=m+1)).image (pairedTupleLabels x y g)=Finset.univ.image y := by
  rw [pairedBasePositions,Finset.image_image]
  apply congrArg (fun f : Fin (m+1) → V => Finset.univ.image f)
  funext i
  exact (pairedTupleLabels_free x y g i 0).trans (Fin.cons_zero _ _)

theorem pairedTupleLabels_zero (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V) (i : Fin (m+1)) :
    (pairedZeroPositions i).image (pairedTupleLabels x y g)=insert (y i) (Finset.univ.image (g i)) := by
  rw [pairedZeroPositions,Finset.image_image]
  have he : pairedTupleLabels x y g ∘ pairedFreePosition i=Fin.cons (α:=fun _ => V) (y i) (g i) := by
    funext j
    exact pairedTupleLabels_free x y g i j
  rw [he]
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨j,hj⟩
    revert hj
    refine Fin.cases ?_ (fun j => ?_) j
    · intro hh
      exact Or.inl hh.symm
    · intro hh
      exact Or.inr ⟨j,hh⟩
  · rintro (rfl|⟨j,hj⟩)
    · exact ⟨0,Fin.cons_zero _ _⟩
    · exact ⟨j.succ,by simpa only [Fin.cons_succ] using hj⟩

theorem pairedTupleLabels_one (x y : Fin (m+1) → V) (g : Fin (m+1) → Fin m → V) (i : Fin (m+1)) :
    (pairedOnePositions i).image (pairedTupleLabels x y g)=insert (x i) (Finset.univ.image (g i)) := by
  ext v
  simp only [Finset.mem_image,Finset.mem_insert,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨p,hp,rfl⟩
    rcases (pairedOnePositions_mem i p).mp hp with rfl|⟨j,hj,rfl⟩
    · exact Or.inl rfl
    · obtain ⟨l,rfl⟩ := Fin.eq_succ_of_ne_zero hj
      exact Or.inr ⟨l,by simp only [pairedTupleLabels_free,Fin.cons_succ]⟩
  · rintro (rfl|⟨j,rfl⟩)
    · exact ⟨pairedRootPosition i,(pairedOnePositions_mem _ _).mpr (Or.inl rfl),rfl⟩
    · refine ⟨pairedFreePosition i j.succ,(pairedOnePositions_mem _ _).mpr (Or.inr ⟨j.succ,Fin.succ_ne_zero _,rfl⟩),?_⟩
      simp only [pairedTupleLabels_free,Fin.cons_succ]

end Oberwolfach
