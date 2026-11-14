module

public import Oberwolfach.FiniteCoordinateEvents
public import Oberwolfach.FiniteMedian
public import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public section

/-! One simultaneous tentative-colouring round. A vertex keeps its colour
exactly when none of its neighbours chose that colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V C : Type*}

def tentativeColourSurvives (G : SimpleGraph V) (σ : V → C) (v : V) : Prop :=
  ∀ u,G.Adj v u → σ u≠σ v

def retainedColour (G : SimpleGraph V) (σ : V → C) (v : V) : Option C :=
  if tentativeColourSurvives G σ v then some (σ v) else none

theorem retainedColour_eq_some (G : SimpleGraph V) (σ : V → C) (v : V) (c : C) :
    retainedColour G σ v=some c ↔ σ v=c ∧ tentativeColourSurvives G σ v := by
  unfold retainedColour
  split_ifs <;> simp_all

theorem retainedColour_none (G : SimpleGraph V) (σ : V → C) (v : V) :
    retainedColour G σ v=none ↔ ∃ u,G.Adj v u ∧ σ u=σ v := by
  simp [retainedColour,tentativeColourSurvives]

theorem retainedColour_proper (G : SimpleGraph V) (σ : V → C)
    {u v : V} (h : G.Adj u v) (c : C)
    (hu : retainedColour G σ u=some c) : retainedColour G σ v≠some c := by
  intro hv
  obtain ⟨huc,hus⟩ := (retainedColour_eq_some G σ u c).mp hu
  obtain ⟨hvc,_⟩ := (retainedColour_eq_some G σ v c).mp hv
  exact hus v h (hvc.trans huc.symm)

theorem tentativeColour_probability [Fintype V] [DecidableEq V] [Fintype C]
    (G : SimpleGraph V) (μ : V → FiniteLaw C) (v : V) (c : C) :
    (FiniteLaw.pi μ).probability
      (fun σ=>σ v=c ∧ tentativeColourSurvives G σ v)=
      (μ v).mass c*∏ u∈Finset.univ.filter (fun u=>G.Adj v u),(1-(μ u).mass c) := by
  classical
  let A : V → C → Prop := fun u a=>
    if u=v then a=c else if G.Adj v u then a≠c else True
  have hevent (σ : V → C) :
      (σ v=c ∧ tentativeColourSurvives G σ v) ↔ ∀ u,A u (σ u) := by
    constructor
    · rintro ⟨hroot,hkeep⟩ u
      by_cases hu : u=v
      · simp [A,hu,hroot]
      · by_cases ha : G.Adj v u
        · simpa [A,hu,ha,hroot] using hkeep u ha
        · simp [A,hu,ha]
    · intro h
      have hroot : σ v=c := by simpa [A] using h v
      refine ⟨hroot,?_⟩
      intro u hu
      have huv : u≠v := fun he=>G.irrefl (he ▸ hu)
      simpa [A,huv,hu,hroot] using h u
  rw [finiteLaw_probability_congr (FiniteLaw.pi μ) _ _ hevent,
    finiteLaw_pi_probability_forall μ A]
  have hcoord (u : V) :
      (μ u).probability (A u)=
        if u=v then (μ v).mass c else if G.Adj v u then 1-(μ u).mass c else 1 := by
    by_cases hu : u=v
    · subst u
      simp only [A,ite_true]
      exact finiteLaw_probability_point _ _
    · by_cases ha : G.Adj v u
      · simp only [A,hu,ite_false,ha,ite_true]
        exact finiteLaw_probability_not_point _ _
      · simp only [A,hu,ite_false,ha]
        exact finiteLaw_probability_true _
  simp_rw [hcoord]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun u=>if u=v then (μ v).mass c else if G.Adj v u then 1-(μ u).mass c else 1)
    (Finset.mem_univ v)]
  simp only [ite_true]
  congr 1
  have he : (Finset.univ.erase v).filter (fun u=>G.Adj v u)=
      Finset.univ.filter (fun u=>G.Adj v u) := by
    ext u
    simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,true_and]
    constructor
    · exact fun h=>h.2
    · intro h
      exact ⟨fun he=>G.irrefl (he ▸ h),h⟩
  calc
    _ = ∏ u∈Finset.univ.erase v,if G.Adj v u then 1-(μ u).mass c else 1 := by
      apply Finset.prod_congr rfl
      intro u hu
      simp only [(Finset.mem_erase.mp hu).1,ite_false]
    _ = ∏ u∈(Finset.univ.erase v).filter (fun u=>G.Adj v u),(1-(μ u).mass c) := by
      rw [Finset.prod_filter]
    _ = _ := by rw [he]

end Oberwolfach
