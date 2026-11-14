module

public import Oberwolfach.LongAssignedHostMatchingWeights
public import Oberwolfach.LongRegularHostVortex
public import Oberwolfach.LongRegularHostNumericInputs

@[expose] public section
/-! Construct host weights and a vortex with one compatible permutation,
keeping the weight constants, vortex size, and host threshold in order. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem long_host_matching_vortex_complete_inputs (L₀:ℕ) (αHost:ℝ) (hα:0<αHost):
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αHost/4≤1/2+αHost/2 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
    ∀K d:ℕ,0<K→2≤d→
    ∃BO:Fin K→ℝ,(∀i,0<BO i) ∧
    ∀βQ εQ ρ₀:ℝ,0<βQ→0<εQ→εQ<1/4→0<ρ₀→
    ∀mLevel:ℕ,∃vsize:ℕ,1≤vsize ∧ mLevel≤vsize ∧
    ∀τ:ℝ,0<τ→∃N:ℕ,0<N ∧
    ∀Allowed:Set ℕ,Allowed.Nonempty→(∀s∈Allowed,3≤s)→
    ∀n:ℕ,max N (2*vsize)≤n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
      (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ)
      (hclass:∀u,factorPreparationClass (F u) K=none)
      (G:SimpleGraph (Fin n)) (D:ℕ) (hreg:G.IsRegularOfDegree D)
      (hmin:(allowedThreshold Allowed+αHost)*n≤(D:ℝ))
      (hρlo:ρ₀≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    ∃Q:Vortex U G D βQ εQ vsize,∃π:Equiv.Perm (Fin n),
      (∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) ∧
      (∀x l,0<l→l<2*d+1→(π^l) x≠x) ∧
      Fintype.card U≤n ∧ 0<D ∧ 0<(D:ℝ) ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧
      (1/2+αHost)*n≤(D:ℝ) ∧ initialIndexDensity U D*(D:ℝ)=2*Fintype.card U ∧
      (∀x,|(G.degree x:ℝ)-(D:ℝ)|≤(0:ℝ)*n) ∧ 2*vsize≤n ∧
      Q.length-1+1=Q.length ∧
    ∃w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ,
    ∃wK:(Fin (m+1)→Fin n)→ℝ,
      (∀i C,0≤w i C ∧ w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,
        5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ ∧
        6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))≤τ*D) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BM wK := by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hhost⟩:=
    long_assigned_host_matching_weights L₀ αHost hα
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,?_⟩
  intro K d hK hd
  obtain ⟨BO,hBO,hweights⟩:=hhost K d hK hd
  refine ⟨BO,hBO,?_⟩
  intro βQ εQ ρ₀ hb he he1 hρ₀ mLevel
  obtain ⟨m₀,hm₀,hvortex⟩:=long_regular_host_vortex_with_permutation αHost βQ εQ ρ₀ hα hb he he1 hρ₀ d
  refine ⟨max m₀ mLevel,le_trans hm₀ (Nat.le_max_left _ _),Nat.le_max_right _ _,?_⟩
  intro τ hτ
  obtain ⟨ε,hε,_,N,hN,hweights⟩:=hweights τ hτ
  refine ⟨N,hN,?_⟩
  intro Allowed hAllowedSet hvalid n hn U _ F hF hAllowed θ hθ hθmax hcut hclass G D hreg hmin hρlo hρhi
  have hnN:N≤n:=le_trans (Nat.le_max_left _ _) hn
  have hnsize:2*(max m₀ mLevel)≤n:=le_trans (Nat.le_max_right _ _) hn
  have hnpos:0<n:=lt_of_lt_of_le hN hnN
  have hmle:max m₀ mLevel≤n:=by omega
  obtain ⟨hD,hDlo,hDhi,hDmargin,hdeg0,hsize⟩:=
    long_regular_host_numeric_inputs n D hnpos U Allowed hAllowedSet hvalid αHost hα G hreg hmin
  have hDreal:0<(D:ℝ):=by exact_mod_cast hD
  have hregε:∀v,|(G.degree v:ℝ)-(D:ℝ)|≤ε*n:=by
    intro v
    have hh:=hdeg0 v
    have hnonneg:0≤ε*(n:ℝ):=mul_nonneg hε.le (by positivity)
    linarith
  have hdeg:∀v,(allowedThreshold Allowed+αHost)*(Fintype.card (Fin n):ℝ)≤(G.degree v:ℝ):=by
    intro v
    simpa [hreg v] using hmin
  obtain ⟨Q,π,hpres,hnoshort⟩:=hvortex Allowed hAllowedSet hvalid n hnpos U G D (max m₀ mLevel)
    hreg hmin hρlo hρhi (Nat.le_max_left _ _) hmle
  obtain ⟨w,wK,hbounds,hedge,hbudget,hwK⟩:=hweights n hnN U F hF Allowed hAllowedSet hvalid hAllowed
    θ ρ₀ (initialIndexDensity U D) D hθ hθmax hρ₀ hρlo hρhi hDreal hsize hcut hclass G π
    (by simpa using hDlo) (by simpa using hDhi) (by simpa using hregε) hdeg
  have hUn:(Fintype.card U:ℝ)≤n:=by
    have hh:0≤(1-initialIndexDensity U D)*(D:ℝ):=mul_nonneg (by linarith) hDreal.le
    nlinarith
  have hUnat:Fintype.card U≤n:=by exact_mod_cast hUn
  have hlast:Q.length-1+1=Q.length:=by have hh:=Q.length_pos;omega
  refine ⟨Q,π,hpres,hnoshort,hUnat,hD,hDreal,hDlo,hDhi,hDmargin,hsize,?_,hnsize,hlast,w,wK,hbounds,hedge,?_,hwK⟩
  · simpa using hdeg0
  · intro i hi
    obtain ⟨hE,hV⟩:=hbudget i hi
    have hnonneg:0≤ε*(n:ℝ):=mul_nonneg hε.le (by positivity)
    exact ⟨hE,by linarith⟩
end Oberwolfach
