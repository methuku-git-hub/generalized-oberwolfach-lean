module

public import Oberwolfach.OrdinaryProtectedReservoirHighProbability
public import Oberwolfach.OrdinaryAssignedClassRecipe

@[expose] public section
/-! The uniform reservoir bound instantiated with the actual ordinary
assigned recipe. The reserved spoke probability is exactly rsv for every
hub, while the approximate probabilities retain their factor dependence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
local instance (priority := high) ordinaryAssignedProtectedReservoirFin (n:ℕ):DecidableEq (Fin n):=Classical.decEq _

theorem ordinary_assigned_protected_reservoir_high_probability
    (r d:ℕ) (hr:3≤r) (hd:2≤d) (α pmin smin L ω:ℝ)
    (hα:0<α) (hpmin:0<pmin) (hsmin:0<smin) (hsmin1:smin≤1) (hω:0<ω) (hL:0≤L):
    ∃ εabs εtrans εsample:ℝ,0<εabs ∧ 0<εtrans ∧ 0<εsample ∧
    ∀ m:ℕ,∃ a₀ b₀ t:ℕ,1≤t ∧ ∀ tterm f:ℕ,∃ N:ℕ,
    ∀ n:ℕ,N≤n→∀(U:Type) [Fintype U] [DecidableEq U],
    Fintype.card U≤n → ω*n≤(Fintype.card U:ℝ) →
    ∀ (P Fbad:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
    permutationConflictGraph π (3*d)≤Fbad →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    (∀v,(Fbad.degree v:ℝ)≤L) →
    (∀v,(cycleThreshold r+α)*n≤(P.degree v:ℝ)) →
    ∀ D:ℝ,(n:ℝ)/2≤D → D≤2*n →
    (∀v,|(P.degree v:ℝ)-D|≤εsample*n) →
    ∀ (p:ℝ) (hp:pmin≤p) (hp1:p≤1),
    ∀(Fs:U→SimpleGraph (Fin n)) (hFs:∀u,(Fs u).IsRegularOfDegree 2)
      (K:ℕ) (i₀:Fin K) (rsv θ c:ℝ),
    smin≤rsv → rsv≤1 →
    let q:=ordinaryAssignedMarkedProbability Fs hFs K θ c
    let s:=ordinaryAssignedSpokeProbability Fs hFs K i₀ rsv θ c;
    ∀(hq:∀u j,0≤q u j) (hQ:∀u,∑j,q u j≤1/8)
      (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j≤ intervalUncoveredProbability d (∑j,q u j)),
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _:Sym2 (Fin n)=>p)
      (fun _=>le_trans (le_of_lt hpmin) hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    1-(1/(n:ℝ)+2/(n:ℝ)^2)≤μ.probability (fun σ:RawWheelOutcome (Fin n) U Bool Bool=>
      OrdinaryUniformProtectedReservoirEvent r m tterm f a₀ b₀ εabs
        (rawWheelGraph P σ\Fbad) Fbad (rawWheelSpokes π d σ false)):=by
  obtain ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,hMain⟩:=
    ordinary_uniform_sampled_protected_reservoir_high_probability r d hr hd α pmin smin L ω hα hpmin hsmin hsmin1 hω hL
  refine ⟨εabs,εtrans,εsample,hεabs,hεtrans,hεsample,?_⟩
  intro m
  obtain ⟨a₀,b₀,t,ht,hMain⟩:=hMain m
  refine ⟨a₀,b₀,t,ht,?_⟩
  intro tterm f
  obtain ⟨N,hMain⟩:=hMain tterm f
  refine ⟨N,?_⟩
  intro n hn U _ _ hu hlo P Fbad π hF hnoshort hdeg hP D hD hDhi hnear p hp hp1 Fs hFs K i₀ rsv θ c hrsv hrsv1 q s hq hQ hs hS μ
  have hFalse:∀u,s u false=rsv:=by
    intro u
    simp only [s,ordinaryAssignedSpokeProbability,Bool.false_eq_true,ite_false]
  have hh:=hMain (Fin n) U Bool Bool (by simpa only [Fintype.card_fin] using hn)
    (by simpa only [Fintype.card_fin] using hu) (by simpa only [Fintype.card_fin] using hlo)
    P Fbad π hF hnoshort (by simpa only [Fintype.card_fin] using hdeg)
    (by simpa only [Fintype.card_fin] using hP) D (by simpa only [Fintype.card_fin] using hD)
    (by simpa only [Fintype.card_fin] using hDhi) (by simpa only [Fintype.card_fin] using hnear)
    p hp hp1 q hq hQ s hs hS false
    (by intro u;rw [hFalse u];exact hrsv)
    (by intro u;rw [hFalse u];exact hrsv1) rsv hrsv hFalse
  simpa only [Fintype.card_fin] using hh
end Oberwolfach
