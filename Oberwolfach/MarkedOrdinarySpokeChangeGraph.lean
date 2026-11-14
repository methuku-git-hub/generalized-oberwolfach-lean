module

public import Oberwolfach.MarkedSpokeChangeGraph
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! The marked part is unchanged when only the ordinary colour is changed;
only the ordinary spoke disagreements contribute to the change graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

theorem marked_spoke_change_graph_ordinary_only
    (H H':Bool→V→U→Prop) (hmark:∀x u,H true x u↔H' true x u):
    (∀x:V,(markedSpokeChangeGraph H H').degree (Sum.inl x)=
      (Finset.univ.filter (fun u=>¬(H false x u↔H' false x u))).card) ∧
    (∀u:U,(markedSpokeChangeGraph H H').degree (Sum.inr u)=
      (Finset.univ.filter (fun x=>¬(H false x u↔H' false x u))).card):=by
  obtain ⟨hl,hr⟩:=marked_spoke_change_graph_degrees H H'
  constructor
  · intro x
    rw [hl]
    congr 1
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.exists_bool]
    simp only [hmark x u,not_true,or_false]
  · intro u
    rw [hr]
    congr 1
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Bool.exists_bool]
    simp only [hmark x u,not_true,or_false]

theorem retained_marked_spokes_independent_of_ordinary_colour
    {Γ Color:Type} [Fintype Γ] [Fintype Color]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g₀ g:Γ) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g₀) t) (j j':Color):
    ∀x u,retainedRawMarkedSpokes π d σ g₀ t J g j true x u↔
      retainedRawMarkedSpokes π d σ g₀ t J g j' true x u:=by
  intro x u
  rfl
end Oberwolfach
