module

public import Oberwolfach.OrdinaryUnassignedPairsStartsEvent
public import Oberwolfach.OrdinaryAssignedUnassignedSlack

@[expose] public section
/-! The actual factor marginals supply unassigned-pair availability and
start-count tests before any later sampling stage. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) assignedPairsStartsFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_unassigned_pairs_starts
    (d:ℕ) (hd:2≤d) (θ ζ:ℝ) (hθ:0<θ) (hθ1:θ≤1/100) (hζ:0<ζ)
    (hda:1/θ≤d):
    ∃N:ℕ,∀n≥N,0<n→∀{U:Type} [Fintype U] [DecidableEq U]
    (F:U→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (K:ℕ) (hK:0<K) (i₀:Fin K) (rsv c ρ D:ℝ)
    (hs0:0≤rsv) (hs1:rsv≤1/100) (hc:8≤c) (hρ:0<ρ) (hρ1:ρ≤1) (hD:0<D)
    (hsize:ρ*D=2*(Fintype.card U:ℝ))
    (S:Set ℕ) (hS:∀w,AllowedCycleLengths (F w) S)
    (hsclass:rsv≤1/(2*(K:ℝ))) (hclass:∀w,factorPreparationClass (F w) K=some i₀)
    (hUhi:Fintype.card U≤n) (π:Equiv.Perm (Fin n))
    (hπ:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (p k p₂ k₂ u:ℝ) (hp:0≤p) (hk:0≤k) (hp₂:0≤p₂) (hk₂:0≤k₂) (hu:0≤u)
    (hsum:2*p+2*k+2*p₂+2*k₂+u≤1),
    let q:=ordinaryAssignedMarkedProbability F hF K θ c
    let s:=ordinaryAssignedSpokeProbability F hF K i₀ rsv θ c;
    ∀(hq:∀w g,0≤q w g) (hQ:∀w,∑g,q w g≤1/8)
      (hs:∀w j,0≤s w j) (hSc:∀w,∑j,s w j ≤ intervalUncoveredProbability d (∑g,q w g))
    {R:(∀e:RawWheelCoordinate (Fin n) U,RawExpandedMarkedCoordinateState Bool Bool e)→Type}
    [∀σ,Fintype (R σ)] (ν:∀σ,FiniteLaw (R σ)),
    let μ:=FiniteLaw.pi (rawExpandedMarkedWheelLaw (V:=Fin n) p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum d hd q hq hQ s hs hSc);
    1-ζ≤(μ.sigma ν).probability (fun z=>OrdinaryUnassignedPairsStartsEvent π d (θ/2) q z.1) :=by
  have hspace:1/(8*(d:ℝ))≤(θ/2)/2:=by
    have hθd:1≤(d:ℝ)*θ:=(div_le_iff₀ hθ).1 hda
    have hdR:0<(d:ℝ):=by exact_mod_cast (show 0<d by omega)
    apply (div_le_iff₀ (show 0<8*(d:ℝ) by positivity)).2
    nlinarith
  obtain ⟨N,hN⟩:=expanded_unassigned_pairs_starts_high d hd (θ/2) ζ (by positivity) hζ hspace
  refine ⟨N,?_⟩
  intro n hnN hn U _ _ F hF K hK i₀ rsv c ρ D hs0 hs1 hc hρ hρ1 hD hsize S hS hsclass hclass hUhi π hπ p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q s hq hQ hs hSc R _ ν μ
  have hU0:0<Fintype.card U:=by
    have hh:0<(Fintype.card U:ℝ):=by nlinarith [mul_pos hρ hD]
    exact_mod_cast hh
  have hSlack:=ordinary_assigned_unassigned_slack hn F hF K hK i₀ rsv θ c ρ D d hd hs0 hs1 hθ hθ1 hc hda hρ hρ1 hD hsize S hS hsclass hclass
  have hrem:∀w,θ/2≤1-(∑g,q w g)-(∑j,s w j):=fun w=>(hSlack.1 w).1
  have hh:=hN (Fin n) U Bool (by simpa using hnN) hU0 (by simpa using hUhi) π p k p₂ k₂ u hp hk hp₂ hk₂ hu hsum q hq hQ s hs hSc hrem hπ ν
  exact hh
end Oberwolfach
