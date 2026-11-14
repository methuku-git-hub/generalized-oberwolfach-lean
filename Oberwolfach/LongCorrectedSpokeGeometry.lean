module

public import Oberwolfach.MarkedIntervalSuccessorRootOrEndpoint
public import Oberwolfach.RetainedMarkedRootUniformity
public import Oberwolfach.RetainedMarkedSpokeChanges

@[expose] public section
/-! The completed ordinary spokes and retained marked spokes satisfy the
same type-disjointness and successor separation required by the level chain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem long_corrected_spoke_geometry
    (π:Equiv.Perm V) (d:ℕ) (hd:1≤d) (σ:RawIntervalFamilyOutcome V U Γ Color)
    (g:Γ) (j:Color) (t:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (R:U→Finset V)
    (hend:∀u (i:retainedMarkedIndex π d σ g t J u),(π^d) i.val∉R u):
    let Y:=fun u=>markedIntervalRootSet π (fun _:retainedMarkedIndex π d σ g t J u=>d) Subtype.val
    let H:Bool→V→U→Prop:=fun b v u=>if b then retainedRawMarkedSpokes π d σ g t J g j true v u else v∈R u\Y u;
    (∀v u,¬(H false v u∧H true v u)) ∧
    (∀u v w,H false v u→H true w u→v≠π w):=by
  intro Y H
  have hroot:∀v u,v∈Y u↔retainedRawMarkedSpokes π d σ g t J g j true v u:=by
    intro v u
    exact retained_marked_root_membership π d hd σ g t J u v
  constructor
  · intro v u h
    exact (Finset.mem_sdiff.mp h.1).2 ((hroot v u).mpr h.2)
  · intro u v w hv hw heq
    have hwY: w∈Y u:=(hroot w u).mpr hw
    have hs:=marked_interval_successor_root_or_endpoint π d
      (Subtype.val:retainedMarkedIndex π d σ g t J u→V) w hwY
    rcases hs with hY|⟨i,hi⟩
    · exact (Finset.mem_sdiff.mp hv).2 (heq ▸ hY)
    · have hR:π w∈R u:=heq ▸ (Finset.mem_sdiff.mp hv).1
      exact hend u i (hi ▸ hR)
end Oberwolfach
