module

public import Oberwolfach.OrdinaryMatchingWeightConstants
public import Oberwolfach.OrdinaryMatchingWeightBudgetsEventually
public import Oberwolfach.OrdinaryEligibleHostRegularEventually
public import Oberwolfach.OrdinaryAssignedShortLowerDirectReserve

@[expose] public section
/-! The original regular host and the selected normalized seed weights supply
all fixed weight, host-degree and short-mass inputs for matching at large order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_original_selected_matching_inputs_eventually
    (K m k d:ℕ) (hK:0<K) (hm:7≤m) (hd:2≤d)
    (α θ τ ρ₀:ℝ) (hα:0<α) (hθ:0<θ) (hθ1:θ≤1/100) (hτ:0<τ) (hρ₀:0<ρ₀)
    (hda:1/θ≤d) (B:Fin K→ℝ) (hB:∀i,0<B i):
    let p₀:ℝ:=min (1/2:ℝ) (ρ₀/4)
    let BM:ℝ:=2*(successorWeightUpper k (α/4))/p₀^(2*m+1)
    let BO:Fin K→ℝ:=fun i=>2*B i/p₀^(2*(longPaddedSeedExponent i+2));
    ∃N:ℕ,∀n:ℕ,N≤n→2≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U]
      (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (Allowed:Set ℕ) (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (i₀:Fin K) (rsv:ℝ) (hs0:0≤rsv) (hs1:rsv≤1/100)
      (hClass:OrdinaryClassReserveBound F hF i₀ rsv)
      (P:SimpleGraph (Fin n)) (D:ℕ) (hreg:P.IsRegularOfDegree D) (hD:0<D)
      (θhost:ℝ) (hhost:1/2≤θhost) (hdegree:(θhost+α)*(n:ℝ)≤D)
      (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1)
      (π:Equiv.Perm (Fin n))
      (w:∀i:Fin K,OrdinaryCycle (ordinaryEligibleHost P π d) (longPaddedSeedExponent i+2)→ℝ)
      (hw:∀i C,0≤w i C ∧ w i C≤B i/(n:ℝ)^(longPaddedSeedExponent i))
      (seed:(Fin (m+1)→Fin n)→ℝ)
      (hseed:SuccessorSequenceWeightConditions (ordinaryEligibleHost P π d) π (3*d) D τ
        (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed),
    let c:ℝ:=(m:ℝ)+1
    let wM:=ordinaryAssignedShiftedSeed F hF i₀ rsv θ c D π d m seed
    let wO:=ordinaryAssignedUnshiftedSeed F hF i₀ rsv θ c D (ordinaryEligibleHost P π d) π d w;
      (∀u,(1/2:ℝ)≤ordinaryAssignedShortWeight F hF K i₀ rsv θ c u) ∧
      (∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m) ∧
      (∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(longPaddedSeedExponent i+1)) ∧
      (∀x,|((ordinaryEligibleHost P π d).degree x:ℝ)-D|≤(τ/4)*(n:ℝ)) ∧
      (∀i,6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))+(τ/4)*(n:ℝ)≤τ*D) ∧
      (∀i,5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*(B i)*(2*(3*d))/(n:ℝ)≤τ) :=by
  intro p₀ BM BO
  obtain ⟨Nb,hb⟩:=ordinary_matching_weight_budgets_eventually K d B τ hτ
  obtain ⟨Nh,hh⟩:=ordinary_eligible_host_regular_eventually d (τ/4) (by positivity)
  refine ⟨max Nb Nh,?_⟩
  intro n hn hn2 U _ _ F hF Allowed hAllowed i₀ rsv hs0 hs1 hClass P D hreg hD θhost hhost hdegree hρlo hρhi π w hw seed hseed c wM wO
  have hn0:0<n:=by omega
  have hρ:0 < initialIndexDensity U D:=hρ₀.trans_le hρlo
  have hDr:0<(D:ℝ):=by exact_mod_cast hD
  have hsize:initialIndexDensity U D*(D:ℝ)=2*(Fintype.card U:ℝ):=by
    simp [initialIndexDensity,ne_of_gt hDr]
  have hnR:0≤(n:ℝ):=by positivity
  have hDlo:(n:ℝ)/2≤D:=by
    have hh':=(mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤θhost+α by linarith) hnR).trans hdegree
    nlinarith only [hh']
  let v:Fin n:=⟨0,hn0⟩
  have hDn:D≤n:=by
    have h:=Finset.card_le_univ (P.neighborFinset v)
    simpa [SimpleGraph.card_neighborFinset_eq_degree,hreg v] using h
  have hDhi:(D:ℝ)≤2*n:=by
    have h:(D:ℝ)≤n:=by exact_mod_cast hDn
    linarith
  have hc:8≤c:=by
    dsimp [c]
    have h:8≤m+1:=by omega
    exact_mod_cast h
  have hUpper:0≤successorWeightUpper k (α/4):=(successorWeightConstants_pos k (α/4) (by positivity)).2.le
  have hseedBounds:=ordinary_assigned_named_seed_bounds_candidate_direct_reserve hn0 F hF hK i₀ rsv θ c ρ₀ (initialIndexDensity U D) D d m hd (by omega)
    hs0 hs1 hθ hθ1 hc hda hρ₀ hρlo hρ hρhi hDr hsize Allowed hAllowed hClass (ordinaryEligibleHost P π d) π τ
    (successorWeightLower k (α/4)) (successorWeightUpper k (α/4)) seed hseed hDlo hDhi hUpper B (fun i=>(hB i).le)
    w (fun i C=>(hw i C).1) (fun i C=>(hw i C).2)
  have hshort:=ordinary_assigned_short_weight_lower_direct_reserve hn0 F hF K hK i₀ rsv θ c hs0 hs1 hθ.le hθ1 hc hClass
  have hweights:=hb n (by omega) hn0 D hDlo
  refine ⟨hshort,?_,?_,hh n (by omega) P D hreg π,hweights.1,hweights.2⟩
  · simpa only [p₀,BM,wM] using hseedBounds.2.1
  · simpa only [p₀,BO,wO] using hseedBounds.2.2
end Oberwolfach
