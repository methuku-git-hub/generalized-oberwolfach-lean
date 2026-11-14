module

public import Oberwolfach.RetainedMarkedSpokeChanges
public import Oberwolfach.RawMarkedSpokeDisjointness

@[expose] public section

/-! Deterministic disjointness of the actual retained spoke types.
Ordinary labels revealed by deletion are tested against the intervals
that remain, using the original ordinary-label coordinate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retainedIntervalCovered_successor_blocked (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d)
    (R : V→Γ→Prop) (v : V) (g : Γ) (hv : retainedIntervalCovered π d R v g) :
    retainedIntervalBlocked π d R (π v) := by
  obtain ⟨a,ha,hva⟩ := hv
  refine ⟨g,a,ha,?_⟩
  obtain ⟨i,hi⟩ := (permutationWindow_mem_iff π 0 (d-1) a v).mp hva
  apply (permutationWindow_mem_iff π 0 d a (π v)).mpr
  refine ⟨⟨i.val+1,by have hh:=i.isLt;omega⟩,?_⟩
  simp only [pow_zero,Equiv.Perm.one_apply] at hi ⊢
  rw [pow_succ',Equiv.Perm.mul_apply,hi]

theorem retainedIntervalState_ordinary_not_blocked (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop) (v : V) (j : Color)
    (h : retainedIntervalState π d σ R v=some (Sum.inr j)) :
    ¬retainedIntervalBlocked π d R v := by
  intro hb
  unfold retainedIntervalState at h
  split_ifs at h <;> simp_all

theorem retainedMarkedSpokes_disjoint (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g : Γ) (j : Color) (v : V) (u : U) :
    ¬(retainedRawMarkedSpokes π d σ g₀ t J g j false v u ∧
      retainedRawMarkedSpokes π d σ g₀ t J g j true v u) := by
  rintro ⟨h₀,hK⟩
  change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j) at h₀
  change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inl g) at hK
  have he := h₀.symm.trans hK
  cases he

theorem retainedMarkedSpokes_successor_disjoint (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g₀ : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (g : Γ) (j : Color) (v : V) (u : U) :
    ¬(retainedRawMarkedSpokes π d σ g₀ t J g j false (π v) u ∧
      retainedRawMarkedSpokes π d σ g₀ t J g j true v u) := by
  rintro ⟨h₀,hK⟩
  have hn := retainedIntervalState_ordinary_not_blocked π d (fun e=>σ (u,e))
    (retainedRawStart π d σ g₀ t J u) (π v) j h₀
  have hc := (retainedIntervalState_interval_iff π d (fun e=>σ (u,e))
    (retainedRawStart π d σ g₀ t J u) (fun _ _ h=>h.1) v g).mp hK
  exact hn (retainedIntervalCovered_successor_blocked π d hd _ v g hc)

end Oberwolfach
