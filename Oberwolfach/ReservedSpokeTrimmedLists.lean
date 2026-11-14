module

public import Oberwolfach.ReservedSpokeExtendingAfterExclusions
public import Oberwolfach.RawReservedSpokeList

@[expose] public section
/-! The free lists remove the inner vertices and absorber targets, while the
old-image disjointness is inherited from the original reserved labels. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_spoke_trimmed_lists
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (D:V→V→Prop) (Inner:Finset V) (Abs Old:U→Finset V) (β lam:ℝ) (hlam:0≤lam)
    (hbudget:∀u,lam*Fintype.card V+Inner.card+(Abs u).card≤β*Fintype.card V)
    (hext:∀u,IsExtendingList D (rawReservedSpokeList π d σ u) β)
    (hOld:∀u,Disjoint (rawReservedSpokeList π d σ u) (Old u)):
    (∀u,IsExtendingList D (rawReservedSpokeList π d σ u\(Inner∪Abs u)) lam) ∧
    (∀u,Disjoint (rawReservedSpokeList π d σ u\(Inner∪Abs u)) (Old u)):=by
  constructor
  · intro u
    exact extending_list_after_two_exclusions D (rawReservedSpokeList π d σ u) Inner (Abs u) β lam hlam (hbudget u) (hext u)
  · intro u
    exact (hOld u).mono_left Finset.sdiff_subset
end Oberwolfach
