module

public import Oberwolfach.ReservedPairAllowedHubs

@[expose] public section
/-! Reserved-pair counts discharge the residual matching's allowed-hub,
outer-hub and old-image shielding conditions. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem reserved_pair_matching_hypotheses
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (inner:Finset U) (Old:U→Finset (Fin n))
    (hOld:∀u,Disjoint (rawReservedSpokeList π d σ u) (Old u))
    (Kbad:SimpleGraph (Fin n)) (Bad:Fin n→Finset U)
    (α a t:ℝ) (hmargin:α*n+inner.card≤a-t)
    (hpair:∀x y,x≠y→a-t≤(((Finset.univ:Finset U).filter (fun u=>
      rawIntervalFamilyState π d σ (x,u)=some (Sum.inr false) ∧
      rawIntervalFamilyState π d σ (y,u)=some (Sum.inr false))).card:ℝ)):
    let Lists:=rawReservedSpokeList π d σ
    let Lbad:=protectedPairEdgeHubs Lists inner
    (∀e,Disjoint (Lbad e) inner) ∧
    (∀u e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old u→u∈Lbad e→u∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,α*n≤((Lbad e).card:ℝ)):=by
  intro Lists Lbad
  obtain ⟨hout,hshield⟩:=protected_pair_edge_hubs_avoid_old_images Lists Old inner hOld
  refine ⟨hout,?_,?_⟩
  · intro u e v he hv ho hu
    exact False.elim (hshield u e v hv ho hu)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy:x≠y:=by
        intro h; subst y
        exact Kbad.loopless.irrefl x (by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he)
      have hh:=reserved_pair_allowed_hubs_lower π d σ inner x y (a-t) (hpair x y hxy)
      change α*n≤((protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner s(x,y)).card:ℝ)
      linarith
end Oberwolfach
