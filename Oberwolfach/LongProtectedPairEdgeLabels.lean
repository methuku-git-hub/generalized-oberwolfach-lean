module

public import Oberwolfach.LongProtectedPairCandidateHubs

@[expose] public section
/-! The canonical protected labels discharge the outer, size, old-shield and
forbidden-hub hypotheses for every edge of a simple bad graph. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_protected_pair_edge_labels
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
      (rawProtectedPairHubs π d σ false true r J x y).card)
    (Kbad:SimpleGraph (Fin n)):
    let Lists:=rawIntervalProtectedUnassignedList π d σ false true r J
    let L:=protectedPairEdgeHubs Lists inner
    (∀e∈Kbad.edgeFinset,Disjoint (L e) inner) ∧
    (∀u e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old u→u∈L e→u∈(∅:Finset U)) ∧
    (∀e∈Kbad.edgeFinset,(2*(5*θ^2*ρ₀/1024))*(n:ℝ)≤(L e).card) ∧
    (∀v:Fin n,(((∅:Finset U).card):ℝ)≤(0:ℝ)*n):=by
  intro Lists L
  obtain ⟨hout,hshield,hcard⟩:=long_protected_pair_candidate_hubs π d hd σ r J Old inner θ ρ₀ ρ D
    hθ hρ₀ hρlo hDlo hsize hspace hN hinner hOld hpair
  refine ⟨fun e _=>hout e,?_,?_,by simp⟩
  · intro u e v he hv ho hu
    exact False.elim (hshield u e v hv ho hu)
  · intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy:x≠y:=by
        intro h
        subst y
        exact Kbad.loopless.irrefl x (by simpa only [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet] using he)
      exact hcard x y hxy

/-- The precise hypotheses consumed by the residual assignment theorem. -/
theorem long_protected_pair_matching_hypotheses
    {n:ℕ} {U Color:Type} [Fintype U] [DecidableEq U] [Fintype Color]
    (π:Equiv.Perm (Fin n)) (d:ℕ) (hd:0<d)
    (σ:RawIntervalFamilyOutcome (Fin n) U Bool Color)
    (r:ℕ) (J:StartRetentionOutcome (rawStartHubSet π d σ false) r)
    (Old:U→Finset (Fin n)) (inner:Finset U) (θ ρ₀ ρ D α b:ℝ)
    (hθ:0<θ) (hρ₀:0<ρ₀) (hρlo:ρ₀≤ρ) (hDlo:(n:ℝ)/2≤D) (hsize:ρ*D=2*Fintype.card U)
    (hspace:1/(4*(d:ℝ))≤(5/64:ℝ)*θ^2)
    (hN:5*(n:ℝ)^(3/4:ℝ)≤(5*θ^2*ρ₀/1024)*n)
    (hinner:(inner.card:ℝ)≤(5*θ^2*ρ₀/1024)*n)
    (hOld:∀u,Disjoint (rawIntervalProtectedUnassignedList π d σ false true r J u) (Old u))
    (hpair:∀x y,x≠y→((5/32:ℝ)*θ^2-1/(4*(d:ℝ)))*Fintype.card U-5*(n:ℝ)^(3/4:ℝ)≤
      (rawProtectedPairHubs π d σ false true r J x y).card)
    (hα:α≤2*(5*θ^2*ρ₀/1024)) (hb:0≤b) (Kbad:SimpleGraph (Fin n)):
    let Lists:=rawIntervalProtectedUnassignedList π d σ false true r J
    let L:=protectedPairEdgeHubs Lists inner
    (∀e∈Kbad.edgeFinset,Disjoint (L e) inner) ∧
    (∀u e v,e∈Kbad.edgeFinset→v∈e.toFinset→v∈Old u→u∈L e→u∈(∅:Finset U)) ∧
    (∀e∈Kbad.edgeFinset,α*(n:ℝ)≤(L e).card) ∧
    (∀v:Fin n,(((∅:Finset U).card):ℝ)≤b*n):=by
  intro Lists L
  obtain ⟨hout,hshield,hcard,hbad⟩:=long_protected_pair_edge_labels π d hd σ r J Old inner θ ρ₀ ρ D
    hθ hρ₀ hρlo hDlo hsize hspace hN hinner hOld hpair Kbad
  refine ⟨hout,hshield,?_,?_⟩
  · intro e he
    exact (mul_le_mul_of_nonneg_right hα (by positivity)).trans (hcard e he)
  · intro v
    simpa using mul_nonneg hb (show (0:ℝ)≤n by positivity)
end Oberwolfach
