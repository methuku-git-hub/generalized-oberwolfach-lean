module

public import Oberwolfach.RawIntervalGeometry

@[expose] public section

/-! Retention removes selected starts, without rerunning activation or
ordinary-label trials. Every changed state is contained in an extended
interval of a removed start. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V Γ Color : Type} [Fintype V] [DecidableEq V]

def retainedIntervalCovered (π : Equiv.Perm V) (d : ℕ) (R : V→Γ→Prop) (x : V) (g : Γ) : Prop :=
  ∃ a,R a g ∧ x∈permutationWindow π 0 (d-1) a

def retainedIntervalBlocked (π : Equiv.Perm V) (d : ℕ) (R : V→Γ→Prop) (x : V) : Prop :=
  ∃ g a,R a g ∧ x∈permutationWindow π 0 d a

def retainedIntervalState (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalOutcome V Γ Color)
    (R : V→Γ→Prop) (x : V) : Option (Γ⊕Color) :=
  if h : ∃ g,retainedIntervalCovered π d R x g then some (Sum.inl (Classical.choose h))
  else if retainedIntervalBlocked π d R x then none
  else (σ (Sum.inr (Sum.inr x))).map Sum.inr

theorem retainedIntervalState_eq_of_no_deletion
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop)
    (hR : ∀ a g,R a g → rawIntervalColouredStart π d σ a g) (x : V)
    (hkeep : ∀ a g,rawIntervalColouredStart π d σ a g → x∈permutationWindow π 0 d a → R a g) :
    retainedIntervalState π d σ R x=rawIntervalState π d σ x := by
  have hc : retainedIntervalCovered π d R x=rawIntervalCovered π d σ x := by
    funext g
    apply propext
    constructor
    · rintro ⟨a,ha,hx⟩;exact ⟨a,hR a g ha,hx⟩
    · rintro ⟨a,ha,hx⟩
      exact ⟨a,hkeep a g ha (permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) a hx),hx⟩
  have hb : retainedIntervalBlocked π d R x=rawIntervalBlocked π d σ x := by
    apply propext
    constructor
    · rintro ⟨g,a,ha,hx⟩;exact ⟨g,a,hR a g ha,hx⟩
    · rintro ⟨g,a,ha,hx⟩;exact ⟨g,a,hkeep a g ha hx,hx⟩
  unfold retainedIntervalState rawIntervalState
  rw [hc,hb]

theorem retainedIntervalState_change_witness
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop)
    (hR : ∀ a g,R a g → rawIntervalColouredStart π d σ a g) (x : V)
    (hchange : retainedIntervalState π d σ R x≠rawIntervalState π d σ x) :
    ∃ a g,rawIntervalColouredStart π d σ a g ∧ ¬R a g ∧ x∈permutationWindow π 0 d a := by
  by_contra hnone
  apply hchange
  apply retainedIntervalState_eq_of_no_deletion π d σ R hR x
  intro a g ha hx
  by_contra hnot
  exact hnone ⟨a,g,ha,hnot,hx⟩

theorem retainedIntervalState_change_selected
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop)
    (hR : ∀ a g,R a g → rawIntervalColouredStart π d σ a g) (g₀ : Γ)
    (hother : ∀ a g,g≠g₀ → rawIntervalColouredStart π d σ a g → R a g) (x : V)
    (hchange : retainedIntervalState π d σ R x≠rawIntervalState π d σ x) :
    ∃ a,rawIntervalColouredStart π d σ a g₀ ∧ ¬R a g₀ ∧ x∈permutationWindow π 0 d a := by
  obtain ⟨a,g,ha,hn,hx⟩ := retainedIntervalState_change_witness π d σ R hR x hchange
  have hg : g=g₀ := by by_contra he;exact hn (hother a g he ha)
  subst g
  exact ⟨a,ha,hn,hx⟩

theorem permutation_power_mem_invariant (π : Equiv.Perm V) (S : Finset V)
    (hS : ∀ x,π x∈S ↔ x∈S) (k : ℕ) (a : V) : (π^k) a∈S ↔ a∈S := by
  induction k with
  | zero=>rfl
  | succ k ih=>simpa only [pow_succ',Equiv.Perm.mul_apply,hS] using ih

theorem permutationWindow_mem_invariant (π : Equiv.Perm V) (S : Finset V)
    (hS : ∀ x,π x∈S ↔ x∈S) (d : ℕ) (a x : V)
    (hx : x∈permutationWindow π 0 d a) : x∈S ↔ a∈S := by
  obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π 0 d a x).mp hx
  simp only [pow_zero,Equiv.Perm.one_apply] at hi
  rw [← hi]
  exact permutation_power_mem_invariant π S hS i.val a

theorem retainedIntervalState_changes_card
    (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop)
    (hR : ∀ a g,R a g → rawIntervalColouredStart π d σ a g) (g₀ : Γ)
    (hother : ∀ a g,g≠g₀ → rawIntervalColouredStart π d σ a g → R a g)
    (S : Finset V) (hS : ∀ x,π x∈S ↔ x∈S) :
    (S.filter (fun x=>retainedIntervalState π d σ R x≠rawIntervalState π d σ x)).card≤
      (d+1)*(S.filter (fun a=>rawIntervalColouredStart π d σ a g₀ ∧ ¬R a g₀)).card := by
  let A := S.filter (fun a=>rawIntervalColouredStart π d σ a g₀ ∧ ¬R a g₀)
  have hsub : S.filter (fun x=>retainedIntervalState π d σ R x≠rawIntervalState π d σ x)⊆
      A.biUnion (fun a=>permutationWindow π 0 d a) := by
    intro x hx
    obtain ⟨hxS,hx⟩ := Finset.mem_filter.mp hx
    obtain ⟨a,ha,hn,hxa⟩ := retainedIntervalState_change_selected π d σ R hR g₀ hother x hx
    apply Finset.mem_biUnion.mpr
    exact ⟨a,Finset.mem_filter.mpr ⟨(permutationWindow_mem_invariant π S hS d a x hxa).mp hxS,ha,hn⟩,hxa⟩
  calc
    _ ≤ (A.biUnion (fun a=>permutationWindow π 0 d a)).card := Finset.card_le_card hsub
    _ ≤ ∑ a∈A,(permutationWindow π 0 d a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a∈A,(d+1) := Finset.sum_le_sum (fun a _=>by simpa using permutationWindow_card_le π 0 d a)
    _ = _ := by simp [A,Nat.mul_comm]

end Oberwolfach
