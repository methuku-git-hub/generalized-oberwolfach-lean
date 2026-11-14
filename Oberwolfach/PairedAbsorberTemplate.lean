module

public import Oberwolfach.AbsorberTemplateGeometry
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-! The paired absorber has one concrete vertex-support template.
Rows are the internal cycles; their first entries form the base cycle.
Replacing a row's first entry by its root gives the other cycles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {c : ℕ} [NeZero c]

def pairedFreePosition (i j : Fin c) : Fin (c*c) ⊕ Fin c := Sum.inl (finProdFinEquiv (i,j))
def pairedRootPosition (i : Fin c) : Fin (c*c) ⊕ Fin c := Sum.inr i

def pairedZeroPositions (i : Fin c) : Finset (Fin (c*c) ⊕ Fin c) :=
  Finset.univ.image (pairedFreePosition i)
def pairedBasePositions : Finset (Fin (c*c) ⊕ Fin c) :=
  Finset.univ.image (fun i : Fin c => pairedFreePosition i 0)
def pairedOnePositions (i : Fin c) : Finset (Fin (c*c) ⊕ Fin c) :=
  Finset.univ.image (fun j : Fin c => if j=0 then pairedRootPosition i else pairedFreePosition i j)

theorem pairedFreePosition_injective : Function.Injective (fun p : Fin c×Fin c => pairedFreePosition p.1 p.2) := by
  intro p q he
  exact finProdFinEquiv.injective (Sum.inl.inj he)

theorem pairedFreePosition_inj {i j k l : Fin c}
    (he : pairedFreePosition i j=pairedFreePosition k l) : (i,j)=(k,l) :=
  finProdFinEquiv.injective (Sum.inl.inj he)

theorem pairedZeroPositions_mem (i : Fin c) (p : Fin (c*c) ⊕ Fin c) :
    p∈pairedZeroPositions i ↔ ∃ j,pairedFreePosition i j=p := by simp [pairedZeroPositions]

theorem pairedBasePositions_mem (p : Fin (c*c) ⊕ Fin c) :
    p∈pairedBasePositions (c:=c) ↔ ∃ i,pairedFreePosition i 0=p := by simp [pairedBasePositions]

theorem pairedOnePositions_mem (i : Fin c) (p : Fin (c*c) ⊕ Fin c) :
    p∈pairedOnePositions i ↔ p=pairedRootPosition i ∨ ∃ j : Fin c,j≠0 ∧ pairedFreePosition i j=p := by
  simp only [pairedOnePositions,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj⟩
    by_cases h : j=0
    · subst j;exact Or.inl (by simpa using hj.symm)
    · exact Or.inr ⟨j,h,by simpa only [h,ite_false] using hj⟩
  · rintro (h | ⟨j,hj,h⟩)
    · exact ⟨0,by simpa using h.symm⟩
    · exact ⟨j,by simpa only [hj,ite_false] using h⟩

theorem paired_zero_positions_card (i : Fin c) : (pairedZeroPositions i).card=c := by
  have hi : Function.Injective (pairedFreePosition i) := by
    intro j k he;exact congrArg Prod.snd (pairedFreePosition_inj he)
  simp only [pairedZeroPositions,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

theorem paired_base_positions_card : (pairedBasePositions (c:=c)).card=c := by
  have hi : Function.Injective (fun i : Fin c => pairedFreePosition i 0) := by
    intro j k he;exact congrArg Prod.fst (pairedFreePosition_inj he)
  simp only [pairedBasePositions,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

theorem paired_one_positions_card (i : Fin c) : (pairedOnePositions i).card=c := by
  have hi : Function.Injective (fun j : Fin c => if j=0 then pairedRootPosition i else pairedFreePosition i j) := by
    intro j k he
    by_cases hj : j=0 <;> by_cases hk : k=0
    · exact hj.trans hk.symm
    · simp [hj,hk,pairedRootPosition,pairedFreePosition] at he
    · simp [hj,hk,pairedRootPosition,pairedFreePosition] at he
    · simp only [hj,hk,ite_false] at he
      exact congrArg Prod.snd (pairedFreePosition_inj he)
  simp only [pairedOnePositions,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

theorem paired_zero_positions_disjoint (i j : Fin c) (hij : i≠j) :
    Disjoint (pairedZeroPositions i) (pairedZeroPositions j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨x,rfl⟩ := (pairedZeroPositions_mem i p).mp hp
  obtain ⟨y,he⟩ := (pairedZeroPositions_mem j _).mp hq
  exact hij (congrArg Prod.fst (pairedFreePosition_inj he)).symm

theorem paired_one_positions_disjoint (i j : Fin c) (hij : i≠j) :
    Disjoint (pairedOnePositions i) (pairedOnePositions j) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  rcases (pairedOnePositions_mem i p).mp hp with hp | ⟨x,hx,hp⟩
  · subst p
    rcases (pairedOnePositions_mem j _).mp hq with hq | ⟨y,hy,hq⟩
    · exact hij (Sum.inr.inj hq)
    · cases hq
  · rcases (pairedOnePositions_mem j p).mp hq with hq | ⟨y,hy,hq⟩
    · rw [hq] at hp;cases hp
    · exact hij (congrArg Prod.fst (pairedFreePosition_inj (hp.trans hq.symm)))

theorem paired_base_one_disjoint (i : Fin c) :
    Disjoint (pairedBasePositions (c:=c)) (pairedOnePositions i) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  obtain ⟨j,rfl⟩ := (pairedBasePositions_mem p).mp hp
  rcases (pairedOnePositions_mem i _).mp hq with hq | ⟨x,hx,hq⟩
  · cases hq
  · exact hx (congrArg Prod.snd (pairedFreePosition_inj hq))

def pairedTemplatePositions : (Fin c ⊕ Fin (c+1)) → Finset (Fin (c*c) ⊕ Fin c)
  | Sum.inl i => pairedZeroPositions i
  | Sum.inr j => Fin.cases pairedBasePositions pairedOnePositions j

theorem paired_template_positions_valid : IsVertexAbsorberTemplate c (pairedTemplatePositions (c:=c)) := by
  refine ⟨?_,paired_zero_positions_disjoint,?_,?_,?_,?_⟩
  · intro o
    rcases o with i | j
    · exact paired_zero_positions_card i
    · refine Fin.cases ?_ (fun i => ?_) j
      · exact paired_base_positions_card
      · exact paired_one_positions_card i
  · intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h;exact (h rfl).elim
      · intro _;exact paired_base_one_disjoint j
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _;exact (paired_base_one_disjoint i).symm
      · intro h;exact paired_one_positions_disjoint i j (fun he => h (congrArg Fin.succ he))
  · ext p
    rcases p with p | p
    · constructor
      · intro _;exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩
      · intro _
        let ij := finProdFinEquiv.symm p
        refine Finset.mem_biUnion.mpr ⟨ij.1,Finset.mem_univ _,?_⟩
        apply (pairedZeroPositions_mem _ _).mpr
        exact ⟨ij.2,by exact congrArg Sum.inl (finProdFinEquiv.apply_symm_apply p)⟩
    · simp [pairedTemplatePositions,pairedZeroPositions,pairedFreePosition]
  · apply Finset.eq_univ_of_forall
    intro p
    rcases p with p | i
    · let ij := finProdFinEquiv.symm p
      have he : pairedFreePosition ij.1 ij.2=Sum.inl p := by exact congrArg Sum.inl (finProdFinEquiv.apply_symm_apply p)
      by_cases hj : ij.2=0
      · refine Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,?_⟩
        change Sum.inl p∈pairedBasePositions
        exact (pairedBasePositions_mem _).mpr ⟨ij.1,by simpa only [hj] using he⟩
      · refine Finset.mem_biUnion.mpr ⟨ij.1.succ,Finset.mem_univ _,?_⟩
        exact (pairedOnePositions_mem _ _).mpr (Or.inr ⟨ij.2,hj,he⟩)
    · refine Finset.mem_biUnion.mpr ⟨i.succ,Finset.mem_univ _,?_⟩
      exact (pairedOnePositions_mem _ _).mpr (Or.inl rfl)
  · intro o
    rcases o with i | j
    · have he : rootLabelPositions (pairedZeroPositions i)=∅ := by
        ext k;simp [rootLabelPositions,pairedZeroPositions,pairedFreePosition]
      change (rootLabelPositions (pairedZeroPositions i)).card ≤ 1
      rw [he];simp
    · refine Fin.cases ?_ (fun i => ?_) j
      · have he : rootLabelPositions (pairedBasePositions (c:=c))=∅ := by
          ext k;simp [rootLabelPositions,pairedBasePositions,pairedFreePosition]
        change (rootLabelPositions (pairedBasePositions (c:=c))).card ≤ 1
        rw [he];simp
      · have he : rootLabelPositions (pairedOnePositions i)={i} := by
          ext k
          simp only [rootLabelPositions,Finset.mem_filter,Finset.mem_univ,true_and,pairedOnePositions_mem,
            pairedRootPosition,pairedFreePosition,Sum.inr.injEq,Sum.inl_ne_inr,and_false,exists_false,or_false,Finset.mem_singleton]
        change (rootLabelPositions (pairedOnePositions i)).card ≤ 1
        rw [he];simp

def pairedAbsorberTemplate (c : ℕ) [NeZero c] : VertexAbsorberTemplate c :=
  ⟨pairedTemplatePositions,paired_template_positions_valid⟩

end Oberwolfach
