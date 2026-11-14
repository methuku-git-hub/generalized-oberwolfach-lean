module

public import Oberwolfach.RawReservedSpokeList
public import Oberwolfach.ProtectedPairAllowedEdges

@[expose] public section
/-! Translate the reserved-colour pair event to allowed outer hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_pair_allowed_hubs_lower
    {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (d:ℕ) (σ:RawIntervalFamilyOutcome V U Bool Bool)
    (inner:Finset U) (x y:V) (a:ℝ)
    (hpair:a≤(((Finset.univ:Finset U).filter (fun u=>
      rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
      rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ)):
    a-inner.card≤((protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner s(x,y)).card:ℝ):=by
  have hc:=protected_pair_edge_hubs_card_lower (rawReservedSpokeList π d σ) inner x y
  have heq:(Finset.univ.filter (fun u=>x∈rawReservedSpokeList π d σ u ∧ y∈rawReservedSpokeList π d σ u))=
      (Finset.univ.filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))):=by
    ext u
    simp [rawReservedSpokeList,rawIntervalOrdinaryOuter]
  rw [heq] at hc
  have hcR:(((Finset.univ:Finset U).filter (fun u=>rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ)≤
      ((protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner s(x,y)).card:ℝ)+inner.card:=by exact_mod_cast hc
  linarith
end Oberwolfach
