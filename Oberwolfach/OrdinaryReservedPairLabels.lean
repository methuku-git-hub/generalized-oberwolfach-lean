module

public import Oberwolfach.ReservedPairMatchingHypotheses

@[expose] public section
/-! The ordinary class's fixed reserve floor supplies allowed hubs for the
required bad edges while excluding protected hubs and old images. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_reserved_pair_matching_labels
    {n:ℕ} {U:Type} [Fintype U] [DecidableEq U]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (σ:RawIntervalFamilyOutcome (Fin n) U Bool Bool)
    (inner:Finset U) (Old:U→Finset (Fin n))
    (hOld:∀u,Disjoint (rawReservedSpokeList π d σ u) (Old u))
    (Kbad:SimpleGraph (Fin n)) (Bad:Fin n→Finset U) (ρ₀ smin:ℝ)
    (hρ:0<ρ₀) (hs:0<smin) (hU:ρ₀*n≤4*(Fintype.card U:ℝ))
    (hinner:(inner.card:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (herror:(n:ℝ)^(3/4:ℝ)≤(5*ρ₀*smin^2/128)*n)
    (hpair:∀x y,x≠y→(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ)≤
      (((Finset.univ:Finset U).filter (fun w=>rawIntervalFamilyState π d σ (x,w)=some (Sum.inr false) ∧
        rawIntervalFamilyState π d σ (y,w)=some (Sum.inr false))).card:ℝ)):
    let a:ℝ:=5*ρ₀*smin^2/128
    let Lbad:=protectedPairEdgeHubs (rawReservedSpokeList π d σ) inner;
    0<a ∧ (∀e,Disjoint (Lbad e) inner) ∧
    (∀w e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old w→w∈Lbad e→w∈Bad v) ∧
    (∀e∈Kbad.edgeFinset,a*n≤((Lbad e).card:ℝ)) :=by
  intro a Lbad
  have ha:0<a:=by dsimp [a];positivity
  have hscale:=mul_le_mul_of_nonneg_left hU (show 0≤(5/32:ℝ)*smin^2 by positivity)
  have hmargin:a*n+inner.card≤(5/8:ℝ)*smin^2*Fintype.card U-(n:ℝ)^(3/4:ℝ):=by
    dsimp [a] at *
    nlinarith
  obtain ⟨hOutside,hShield,hLabels⟩:=reserved_pair_matching_hypotheses π d σ inner Old hOld Kbad Bad a
    ((5/8:ℝ)*smin^2*Fintype.card U) ((n:ℝ)^(3/4:ℝ)) hmargin hpair
  exact ⟨ha,hOutside,hShield,hLabels⟩
end Oberwolfach
