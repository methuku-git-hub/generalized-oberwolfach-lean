module

public import Oberwolfach.RetainedOrdinarySpokesMonotone
public import Oberwolfach.RetainedMarkedSpokeGeometry
public import Oberwolfach.RetainedIntervalIdentities

@[expose] public section
/-! The already occupied labels lie in the other ordinary colour or on
retained marked intervals and their successors, so avoid the selected ordinary
spoke colour. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem retained_ordinary_different_colours_disjoint
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (j j':Color) (hne:j'≠j) (v:V) (u:U):
    ¬(retainedRawMarkedSpokes π d σ g₀ t J g j' false v u ∧
      retainedRawMarkedSpokes π d σ g₀ t J g j false v u):=by
  rintro ⟨h1,h2⟩
  change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j') at h1
  change retainedRawFamilyState π d σ g₀ t J (v,u)=some (Sum.inr j) at h2
  have hh:=h1.symm.trans h2
  exact hne (by simpa only [Option.some.injEq,Sum.inr.injEq] using hh)


theorem raw_other_marked_spoke_survives_start_retention
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (hg:g≠g₀) (j:Color) (v:V) (u:U)
    (h:rawMarkedSpokes π d σ g j true v u):
    retainedRawMarkedSpokes π d σ g₀ t J g j true v u:=by
  have hraw:rawIntervalState π d (fun e=>σ (u,e)) v=some (Sum.inl g):=h
  obtain ⟨a,ha,hv⟩:=(rawIntervalState_interval_iff π d (fun e=>σ (u,e)) v g).mp hraw
  change retainedIntervalState π d (fun e=>σ (u,e)) (retainedRawStart π d σ g₀ t J u) v=some (Sum.inl g)
  apply (retainedIntervalState_interval_iff π d (fun e=>σ (u,e))
    (retainedRawStart π d σ g₀ t J u) (fun _ _ h=>h.1) v g).mpr
  exact ⟨a,⟨ha,fun he=>False.elim (hg he)⟩,hv⟩

theorem marked_occupied_labels_avoid_retained_outer
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (g:Γ) (j j':Color) (hne:j'≠j) (Old:U→Finset V)
    (hold:∀u v,v∈Old u→
      rawMarkedSpokes π d σ g j' false v u ∨
      (∃k,retainedRawMarkedSpokes π d σ g₀ t J k j true v u) ∨
      ∃k x,π x=v ∧ retainedRawMarkedSpokes π d σ g₀ t J k j true x u):
    ∀u,Disjoint (Old u)
      (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g j false v u)):=by
  intro u
  apply Finset.disjoint_left.mpr
  intro v hv houter
  have hout:retainedRawMarkedSpokes π d σ g₀ t J g j false v u:=(Finset.mem_filter.mp houter).2
  rcases hold u v hv with hother|⟨k,hmarked⟩|⟨k,x,rfl,hmarked⟩
  · have hret:=raw_ordinary_spoke_survives_start_retention π d σ g₀ t J g j' v u hother
    exact retained_ordinary_different_colours_disjoint π d σ g₀ t J g j j' hne v u ⟨hret,hout⟩
  · exact retainedMarkedSpokes_disjoint π d σ g₀ t J k j v u ⟨hout,hmarked⟩
  · exact retainedMarkedSpokes_successor_disjoint π d hd σ g₀ t J k j x u ⟨hout,hmarked⟩

theorem marked_occupied_with_raw_approximate_intervals_avoid_outer
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g:Γ) (hg:g≠g₀) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t)
    (j j':Color) (hne:j'≠j) (Old:U→Finset V)
    (hold:∀u v,v∈Old u→
      rawMarkedSpokes π d σ g j' false v u ∨
      rawMarkedSpokes π d σ g j true v u ∨
      (∃x,π x=v ∧ rawMarkedSpokes π d σ g j true x u) ∨
      retainedRawMarkedSpokes π d σ g₀ t J g₀ j true v u ∨
      (∃x,π x=v ∧ retainedRawMarkedSpokes π d σ g₀ t J g₀ j true x u)):
    ∀u,Disjoint (Old u)
      (Finset.univ.filter (fun v=>retainedRawMarkedSpokes π d σ g₀ t J g₀ j false v u)):=by
  apply marked_occupied_labels_avoid_retained_outer π d hd σ g₀ t J g₀ j j' hne Old
  intro u v hv
  rcases hold u v hv with hOrd|hApp|⟨x,hx,hApp⟩|hFin|⟨x,hx,hFin⟩
  · exact Or.inl hOrd
  · exact Or.inr (Or.inl ⟨g,raw_other_marked_spoke_survives_start_retention π d σ g₀ t J g hg j v u hApp⟩)
  · exact Or.inr (Or.inr ⟨g,x,hx,raw_other_marked_spoke_survives_start_retention π d σ g₀ t J g hg j x u hApp⟩)
  · exact Or.inr (Or.inl ⟨g₀,hFin⟩)
  · exact Or.inr (Or.inr ⟨g₀,x,hx,hFin⟩)

end Oberwolfach
