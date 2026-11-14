module

public import Oberwolfach.RawMarkedHubCounts

@[expose] public section

/-! The two raw spoke classes, including the successor of a marked label,
are disjoint at a fixed hub. This is a deterministic property of every raw
outcome, not a consequence of marginal probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem rawIntervalCovered_successor_blocked
    {V Γ Color : Type} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d) (σ : RawIntervalOutcome V Γ Color)
    (x : V) (g : Γ) (hx : rawIntervalCovered π d σ x g) :
    rawIntervalBlocked π d σ (π x) := by
  obtain ⟨a,ha,hxa⟩ := hx
  refine ⟨g,a,ha,?_⟩
  obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π 0 (d-1) a x).mp hxa
  apply (permutationWindow_mem_iff π 0 d a (π x)).mpr
  refine ⟨⟨i.val+1,by have hh:=i.isLt;omega⟩,?_⟩
  simp only [pow_zero,Equiv.Perm.one_apply] at hi ⊢
  rw [pow_succ',Equiv.Perm.mul_apply,hi]

theorem rawMarkedSpokes_disjoint
    {V U Γ Color : Type} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g : Γ) (j : Color) (v : V) (u : U) :
    ¬(rawMarkedSpokes π d σ g j false v u ∧ rawMarkedSpokes π d σ g j true v u) := by
  rintro ⟨h₀,hK⟩
  change rawIntervalFamilyState π d σ (v,u)=some (Sum.inr j) at h₀
  change rawIntervalFamilyState π d σ (v,u)=some (Sum.inl g) at hK
  have h := h₀.symm.trans hK
  cases h

theorem rawMarkedSpokes_successor_disjoint
    {V U Γ Color : Type} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g : Γ) (j : Color) (v : V) (u : U) :
    ¬(rawMarkedSpokes π d σ g j false (π v) u ∧ rawMarkedSpokes π d σ g j true v u) := by
  rintro ⟨h₀,hK⟩
  have hn := (rawIntervalState_label_iff π d (fun e=>σ (u,e)) (π v) j).mp h₀
  have hc := (rawIntervalState_interval_iff π d (fun e=>σ (u,e)) v g).mp hK
  exact hn.1 (rawIntervalCovered_successor_blocked π d hd _ v g hc)

theorem rawMarkedSpokeClasses_disjoint
    {V U Γ Color : Type} [Fintype V] [DecidableEq V]
    (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g : Γ) (j : Color) (u : Fin 2→U) :
    let T := fun b : Bool=>Finset.univ.filter (fun v=>∀ i,rawMarkedSpokes π d σ g j b v (u i))
    Disjoint (T false) (T true) ∧ Disjoint (T false) ((T true).image π) := by
  intro T
  constructor
  · apply Finset.disjoint_left.mpr
    intro v h₀ hK
    exact rawMarkedSpokes_disjoint π d σ g j v (u 0)
      ⟨(Finset.mem_filter.mp h₀).2 0,(Finset.mem_filter.mp hK).2 0⟩
  · apply Finset.disjoint_left.mpr
    intro v h₀ hK
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hK
    exact rawMarkedSpokes_successor_disjoint π d hd σ g j w (u 0)
      ⟨(Finset.mem_filter.mp h₀).2 0,(Finset.mem_filter.mp hw).2 0⟩

end Oberwolfach
