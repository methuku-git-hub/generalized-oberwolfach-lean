module

public import Oberwolfach.RetainedIntervalIndexChanges
public import Oberwolfach.UniformStartRetention

@[expose] public section

/-! Actual interval retention with one trimmed colour. Every other
interval and every primitive ordinary colour are kept unchanged. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

def rawStartHubSet (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g₀ : Γ) (a : V) : Finset U :=
  Finset.univ.filter (fun u=>rawIntervalColouredStart π d (fun e=>σ (u,e)) a g₀)

def retainedRawStart (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g₀ : Γ) (t : ℕ) (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (u : U) (a : V) (g : Γ) : Prop :=
  rawIntervalColouredStart π d (fun e=>σ (u,e)) a g ∧
    (g=g₀ → u∈startRetainedHubs (rawStartHubSet π d σ g₀) t J a)

def retainedRawFamilyState (π : Equiv.Perm V) (d : ℕ) (σ : RawIntervalFamilyOutcome V U Γ Color)
    (g₀ : Γ) (t : ℕ) (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (a : V×U) : Option (Γ⊕Color) :=
  retainedIntervalState π d (fun e=>σ (a.2,e)) (retainedRawStart π d σ g₀ t J a.2) a.1

theorem retainedRawStart_removed_iff (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (u : U) (a : V) :
    (rawIntervalColouredStart π d (fun e=>σ (u,e)) a g₀ ∧ ¬retainedRawStart π d σ g₀ t J u a g₀) ↔
      u∈startRemovedHubs (rawStartHubSet π d σ g₀) t J a := by
  simp only [retainedRawStart,implies_true,forall_const,startRemovedHubs,Finset.mem_sdiff,
    rawStartHubSet,Finset.mem_filter,Finset.mem_univ,true_and]
  tauto

theorem retainedRawFamily_row_changes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (u : U)
    (S : Finset V) (hS : ∀ x,π x∈S ↔ x∈S) :
    (S.filter (fun x=>retainedRawFamilyState π d σ g₀ t J (x,u)≠rawIntervalFamilyState π d σ (x,u))).card≤
      (d+1)*(S.filter (fun a=>u∈startRemovedHubs (rawStartHubSet π d σ g₀) t J a)).card := by
  have hh := retainedIntervalState_changes_card π d (fun e=>σ (u,e)) (retainedRawStart π d σ g₀ t J u)
    (fun _ _ h=>h.1) g₀ (fun a g hg h=>⟨h,fun he=>False.elim (hg he)⟩) S hS
  simpa only [retainedRawStart_removed_iff,retainedRawFamilyState,rawIntervalFamilyState] using hh

theorem retainedRawFamily_index_changes (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (x : V) (T : Finset U) :
    (T.filter (fun u=>retainedRawFamilyState π d σ g₀ t J (x,u)≠rawIntervalFamilyState π d σ (x,u))).card≤
      ∑ a∈permutationWindow π d 0 x,(T∩startRemovedHubs (rawStartHubSet π d σ g₀) t J a).card := by
  have hh := retainedInterval_index_changes_card π d σ (retainedRawStart π d σ g₀ t J)
    (fun _ _ _ h=>h.1) g₀ (fun u a g hg h=>⟨h,fun he=>False.elim (hg he)⟩) x T
  simp only [retainedRawStart_removed_iff] at hh
  have he : ∀ a,T.filter (fun u=>u∈startRemovedHubs (rawStartHubSet π d σ g₀) t J a)=
      T∩startRemovedHubs (rawStartHubSet π d σ g₀) t J a := by intro a;ext u;simp
  simpa only [he,retainedRawFamilyState] using hh

end Oberwolfach
