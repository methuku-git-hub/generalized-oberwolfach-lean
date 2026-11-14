module

public import Oberwolfach.PermutationEmbeddingWindows
public import Oberwolfach.RawIntervalGeometry

@[expose] public section

/-! Interval labels on a permutation-invariant domain agree with the labels
of the original sample. Invariance is used for every competing start in the
whole permutation window, not only for the observed root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V W Γ Color : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def rawIntervalRestrictVertices (f : W→V) (σ : RawIntervalOutcome V Γ Color) : RawIntervalOutcome W Γ Color
  | Sum.inl x=>σ (Sum.inl (f x))
  | Sum.inr (Sum.inl x)=>σ (Sum.inr (Sum.inl (f x)))
  | Sum.inr (Sum.inr x)=>σ (Sum.inr (Sum.inr (f x)))

variable (f : W→V) (hf : Function.Injective f) (π : Equiv.Perm V) (ρ : Equiv.Perm W)
  (hcomm : ∀ x,f (ρ x)=π (f x))
include hf hcomm

theorem rawIntervalKept_restrict (d : ℕ) (A : V→Bool) (a : W) :
    rawIntervalKept ρ d (fun x=>A (f x)) a ↔ rawIntervalKept π d A (f a) := by
  constructor
  · rintro ⟨ha,h⟩
    refine ⟨ha,?_⟩
    intro b hb hba
    rw [← permutationWindow_image f π ρ hcomm d d a] at hb
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hb
    exact h z hz (fun he=>hba (congrArg f he))
  · rintro ⟨ha,h⟩
    refine ⟨ha,?_⟩
    intro b hb hba
    exact h (f b) ((permutationWindow_embedding_mem f π ρ hcomm hf d d a b).mpr hb)
      (fun he=>hba (hf he))

theorem rawIntervalColouredStart_restrict (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (a : W) (g : Γ) :
    rawIntervalColouredStart ρ d (rawIntervalRestrictVertices f σ) a g ↔
      rawIntervalColouredStart π d σ (f a) g := by
  exact and_congr (rawIntervalKept_restrict f hf π ρ hcomm d (fun x=>σ (Sum.inl x)) a) Iff.rfl

theorem rawIntervalCovered_restrict (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (x : W) (g : Γ) :
    rawIntervalCovered ρ d (rawIntervalRestrictVertices f σ) x g ↔ rawIntervalCovered π d σ (f x) g := by
  constructor
  · rintro ⟨a,ha,hx⟩
    exact ⟨f a,(rawIntervalColouredStart_restrict f hf π ρ hcomm d σ a g).mp ha,
      (permutationWindow_embedding_mem f π ρ hcomm hf 0 (d-1) a x).mpr hx⟩
  · rintro ⟨a,ha,hx⟩
    have ha' := (permutationWindow_dual π 0 (d-1) a (f x)).mp hx
    rw [← permutationWindow_image f π ρ hcomm (d-1) 0 x] at ha'
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha'
    exact ⟨z,(rawIntervalColouredStart_restrict f hf π ρ hcomm d σ z g).mpr ha,
      (permutationWindow_embedding_mem f π ρ hcomm hf 0 (d-1) z x).mp hx⟩

theorem rawIntervalBlocked_restrict (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (x : W) :
    rawIntervalBlocked ρ d (rawIntervalRestrictVertices f σ) x ↔ rawIntervalBlocked π d σ (f x) := by
  constructor
  · rintro ⟨g,a,ha,hx⟩
    exact ⟨g,f a,(rawIntervalColouredStart_restrict f hf π ρ hcomm d σ a g).mp ha,
      (permutationWindow_embedding_mem f π ρ hcomm hf 0 d a x).mpr hx⟩
  · rintro ⟨g,a,ha,hx⟩
    have ha' := (permutationWindow_dual π 0 d a (f x)).mp hx
    rw [← permutationWindow_image f π ρ hcomm d 0 x] at ha'
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp ha'
    exact ⟨g,z,(rawIntervalColouredStart_restrict f hf π ρ hcomm d σ z g).mpr ha,
      (permutationWindow_embedding_mem f π ρ hcomm hf 0 d z x).mp hx⟩

theorem rawIntervalState_restrict (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (x : W) :
    rawIntervalState ρ d (rawIntervalRestrictVertices f σ) x=rawIntervalState π d σ (f x) := by
  apply Option.ext
  intro a
  cases a with
  | inl g=>
    simpa only [Option.mem_def,eq_comm,rawIntervalState_interval_iff] using
      rawIntervalCovered_restrict f hf π ρ hcomm d σ x g
  | inr j=>
    simp only [Option.mem_def,eq_comm,rawIntervalState_label_iff,
      rawIntervalBlocked_restrict f hf π ρ hcomm,rawIntervalRestrictVertices]

end Oberwolfach
