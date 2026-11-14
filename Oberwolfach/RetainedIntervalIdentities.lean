module

public import Oberwolfach.RetainedIntervalFamily

@[expose] public section

/-! Exact retained interval degrees: each start occurs at t hubs and each
vertex is covered at d*t hubs. These are deterministic identities of the
retained sample, not expectation statements. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retainedIntervalCovered_unique (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop)
    (hR : ∀ a g,R a g → rawIntervalColouredStart π d σ a g) (x : V) (g h : Γ)
    (hg : retainedIntervalCovered π d R x g) (hh : retainedIntervalCovered π d R x h) : g=h := by
  obtain ⟨a,ha,hxa⟩ := hg
  obtain ⟨b,hb,hxb⟩ := hh
  exact rawIntervalCovered_unique π d σ x g h ⟨a,hR a g ha,hxa⟩ ⟨b,hR b h hb,hxb⟩

theorem retainedIntervalState_interval_iff (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalOutcome V Γ Color) (R : V→Γ→Prop)
    (hR : ∀ a g,R a g → rawIntervalColouredStart π d σ a g) (x : V) (g : Γ) :
    retainedIntervalState π d σ R x=some (Sum.inl g) ↔ retainedIntervalCovered π d R x g := by
  unfold retainedIntervalState
  split_ifs with hg hb
  · have hh := Classical.choose_spec hg
    constructor
    · intro he
      have he' : Classical.choose hg=g := Sum.inl.inj (Option.some.inj he)
      exact he' ▸ hh
    · intro he
      rw [retainedIntervalCovered_unique π d σ R hR x _ _ hh he]
  · constructor
    · intro he;cases he
    · intro he;exact (hg ⟨g,he⟩).elim
  · constructor
    · intro he
      cases hc : σ (Sum.inr (Sum.inr x)) <;> simp [hc] at he
    · intro he;exact (hg ⟨g,he⟩).elim

theorem retainedRawStart_selected_iff (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g) t) (u : U) (a : V) :
    retainedRawStart π d σ g t J u a g ↔ u∈startRetainedHubs (rawStartHubSet π d σ g) t J a := by
  constructor
  · intro h;exact h.2 rfl
  · intro h
    have ha := startRetainedHubs_subset (rawStartHubSet π d σ g) t J a h
    have hr : rawIntervalColouredStart π d (fun e=>σ (u,e)) a g := (Finset.mem_filter.mp ha).2
    exact ⟨hr,fun _=>h⟩

theorem retainedRawStart_card (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g) t) (a : V) :
    (Finset.univ.filter (fun u=>retainedRawStart π d σ g t J u a g)).card=t := by
  simp only [retainedRawStart_selected_iff,Finset.filter_mem_eq_inter,Finset.univ_inter]
  exact startRetainedHubs_card _ _ _ _

theorem retainedRawFamily_covered_hubs (π : Equiv.Perm V) (d : ℕ)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g) t) (x : V) :
    Finset.univ.filter (fun u=>retainedRawFamilyState π d σ g t J (x,u)=some (Sum.inl g))=
      (permutationWindow π (d-1) 0 x).biUnion (fun a=>startRetainedHubs (rawStartHubSet π d σ g) t J a) := by
  ext u
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_biUnion,retainedRawFamilyState]
  rw [retainedIntervalState_interval_iff π d (fun e=>σ (u,e)) (retainedRawStart π d σ g t J u)
    (fun _ _ h=>h.1)]
  simp only [retainedIntervalCovered,retainedRawStart_selected_iff,permutationWindow_dual]
  constructor
  · rintro ⟨a,ha,hxa⟩;exact ⟨a,hxa,ha⟩
  · rintro ⟨a,hxa,ha⟩;exact ⟨a,ha,hxa⟩

theorem retainedRawFamily_covered_card (π : Equiv.Perm V) (d : ℕ) (hd : 1≤d)
    (hnoshort : ∀ x l,0<l → l<d → (π^l) x≠x)
    (σ : RawIntervalFamilyOutcome V U Γ Color) (g : Γ) (t : ℕ)
    (J : StartRetentionOutcome (rawStartHubSet π d σ g) t) (x : V) :
    (Finset.univ.filter (fun u=>retainedRawFamilyState π d σ g t J (x,u)=some (Sum.inl g))).card=d*t := by
  rw [retainedRawFamily_covered_hubs]
  have hdisj : ((permutationWindow π (d-1) 0 x : Finset V):Set V).PairwiseDisjoint
      (fun a=>startRetainedHubs (rawStartHubSet π d σ g) t J a) := by
    intro a ha b hb hne
    apply Finset.disjoint_left.mpr
    intro u hua hub
    have hra := (retainedRawStart_selected_iff π d σ g t J u a).mpr hua
    have hrb := (retainedRawStart_selected_iff π d σ g t J u b).mpr hub
    have hxa := (permutationWindow_dual π (d-1) 0 x a).mp ha
    have hxb := (permutationWindow_dual π (d-1) 0 x b).mp hb
    exact hne (rawInterval_coloured_start_unique π d (fun e=>σ (u,e)) x a b g g hra.1 hrb.1
      (permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) a hxa)
      (permutationWindow_mono π (le_refl 0) (Nat.sub_le d 1) b hxb)).1
  rw [Finset.card_biUnion hdisj]
  simp only [startRetainedHubs_card,Finset.sum_const,nsmul_eq_mul]
  have hc : (permutationWindow π (d-1) 0 x).card=d := by
    have hh := permutationWindow_card π (d-1) 0 (by intro y l hl hld;exact hnoshort y l hl (by omega)) x
    simpa only [Nat.add_zero,Nat.sub_add_cancel hd] using hh
  simp only [hc,Nat.cast_id]

end Oberwolfach
