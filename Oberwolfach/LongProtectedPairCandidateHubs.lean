module

public import Oberwolfach.RawProtectedPairHubLower
public import Oberwolfach.ProtectedPairAllowedEdges

@[expose] public section
/-! Turn the protected-pair event into explicit linearly large allowed edge
labels, excluding inner hubs and automatically shielding old images. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_protected_pair_candidate_hubs
    {n:ℕ} {U Color:Type} [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:0<d)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Color)
    (r:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (Old:U→Finset (Fin n)) (inner:Finset U) (θ ρ₀ ρ D:ℝ)
    (hθ:0<θ) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hDlo:(n:ℝ)/2≤D) (hsize:ρ*D=2*Fintype.card U)
    (hspace:1/(4*(d:ℝ))≤(5/64:ℝ)*θ^2)
    (hN:5*(n:ℝ)^(3/4:ℝ)≤(5*θ^2*ρ₀/1024)*n)
    (hinner:(inner.card:ℝ)≤(5*θ^2*ρ₀/1024)*n)
    (hOld:∀u,Disjoint (rawIntervalProtectedUnassignedList π d σ false true r J u) (Old u))
    (hpair:∀x y,x≠y→((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U-5*(n:ℝ)^(3/4:ℝ)≤
      (rawProtectedPairHubs π d σ false true r J x y).card):
    let Lists:=rawIntervalProtectedUnassignedList π d σ false true r J
    let L:=protectedPairEdgeHubs Lists inner
    (∀e,Disjoint (L e) inner) ∧
    (∀u e v,v∈e.toFinset→v∈Old u→u∈L e→False) ∧
    (∀x y,x≠y→(2*(5*θ^2*ρ₀/1024))*(n:ℝ)≤(L s(x,y)).card):=by
  intro Lists L
  obtain ⟨hout,hshield⟩:=protected_pair_edge_hubs_avoid_old_images Lists Old inner hOld
  refine ⟨hout,hshield,?_⟩
  intro x y hxy
  have hn:(0:ℝ)≤n:=by positivity
  have hD0:0≤D:=le_trans (by positivity) hDlo
  have hρ0:0≤ρ:=le_trans hρ₀.le hρlo
  have hleft:ρ₀*(n:ℝ)/4≤(Fintype.card U:ℝ):=by
    have hh:=mul_le_mul hρlo hDlo (by positivity) hρ0
    linarith [hsize]
  have hcoeff:(5/64:ℝ)*θ^2≤(5/32:ℝ)*θ^2-1/(4*(d:ℝ)):=by linarith
  have hp:(0:ℝ)≤(5/64:ℝ)*θ^2:=by positivity
  have ha:=mul_le_mul_of_nonneg_right hcoeff (show (0:ℝ)≤Fintype.card U by positivity)
  have hb:=mul_le_mul_of_nonneg_left hleft hp
  have hscale:=hb.trans ha
  have hh:=hpair x y hxy
  have hc:=protected_pair_edge_hubs_card_lower Lists inner x y
  have hc':(rawProtectedPairHubs π d σ false true r J x y).card≤(L s(x,y)).card+inner.card:=by
    simpa only [rawProtectedPairHubs,Lists,L] using hc
  have hcR:((rawProtectedPairHubs π d σ false true r J x y).card:ℝ)≤(L s(x,y)).card+inner.card:=by exact_mod_cast hc'
  nlinarith [hscale,hN,hinner,hcR,hh]
end Oberwolfach
