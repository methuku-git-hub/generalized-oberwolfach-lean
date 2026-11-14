module

public import Oberwolfach.RetentionRestrictionLocalEvent

@[expose] public section
/-! A global retention test implies its restriction when the global error
is scaled below the size of the chosen vertex set. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem retained_restriction_local_from_global
    {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
    [DecidableEq V] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Γ Color) (g:Γ) (t:ℕ)
    (A:Finset V) (ζglobal ζlocal:ℝ)
    (J:StartRetentionOutcome (rawStartHubSet π d σ g) t)
    (hglobal:RetainedRestrictionGood π d σ g t (fun _:Unit=>Finset.univ) (fun _:Unit=>Finset.univ) ζglobal J)
    (hcol:ζglobal*Fintype.card V≤ζlocal*A.card) (hrow:ζglobal≤ζlocal):
    RetainedRestrictionLocalGood π d σ g t A Finset.univ ζlocal J :=by
  constructor
  · intro w hw
    have hsub:(A.filter (fun x=>retainedRawFamilyState π d σ g t J (x,w)≠rawIntervalFamilyState π d σ (x,w)))⊆
        Finset.univ.filter (fun x=>retainedRawFamilyState π d σ g t J (x,w)≠rawIntervalFamilyState π d σ (x,w)):=
      Finset.filter_subset_filter _ (Finset.subset_univ A)
    have hcard:((A.filter (fun x=>retainedRawFamilyState π d σ g t J (x,w)≠rawIntervalFamilyState π d σ (x,w))).card:ℝ)≤
        ((Finset.univ.filter (fun x=>retainedRawFamilyState π d σ g t J (x,w)≠rawIntervalFamilyState π d σ (x,w))).card:ℝ):=by exact_mod_cast Finset.card_le_card hsub
    have hh:= (hglobal ()).1 w
    simpa only [Finset.card_univ] using (hcard.trans (hh.trans hcol))
  · intro x hx
    have hh:=(hglobal ()).2 x
    have hr:=mul_le_mul_of_nonneg_right hrow (show (0:ℝ)≤Fintype.card U by positivity)
    simpa only [Finset.card_univ] using hh.trans hr
end Oberwolfach
