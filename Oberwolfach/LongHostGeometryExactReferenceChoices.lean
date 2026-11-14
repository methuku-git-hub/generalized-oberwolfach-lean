module

public import Oberwolfach.LongHostMatchingVortexGeometricInputs
public import Oberwolfach.LongHostAdaptiveExactReferenceParameters

@[expose] public section
/-! Choose the host weights, exact reference scales, and geometric-vortex
continuation in the dependency order needed by the matching construction. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def LongHostMatchingGeometryContinuation
    (m K d:ℕ) (αHost A BM:ℝ) (BO:Fin K→ℝ):Prop :=
    ∀βQ εQ ρ₀:ℝ,0<βQ→0<εQ→εQ<1/4→0<ρ₀→
    ∀ (κ hIcut ξ xiDeep ω x:ℝ) (Ngeom NIgeom:ℕ),1≤Ngeom →
      εQ≤1/8 → εQ≤αHost/8 → εQ≤κ → εQ≤hIcut → 4*εQ≤ξ → εQ^2≤xiDeep →
      0≤ω → ω≤εQ/8 → ω≤ρ₀*εQ/64 →
      βQ≤1/4 → βQ≤αHost/8 → βQ≤3*αHost/40 → βQ≤3/20 → βQ≤κ → βQ≤x →
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
      (∀L:ℕ,L<Q.length→MarkedVortexGeometricRecordEvent Q αHost ρ₀ κ hIcut ξ xiDeep ω x Ngeom NIgeom L) ∧
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
      SuccessorSequenceWeightConditions G π (3*d) D τ A BM wK

theorem long_host_geometry_exact_reference_choices
    (L₀:ℕ) (αHost:ℝ) (hα:0<αHost):
    ∃m r k₀:ℕ,7≤m ∧ L₀≤m ∧ Even (m+1) ∧ 2≤r ∧ r+4=m ∧
      r+4+1=(k₀+2)*2 ∧ successorCycleRatio k₀+αHost/4≤1/2+αHost/2 ∧
    ∃A BM:ℝ,0<A ∧ 0<BM ∧
    ∀ρ₀:ℝ,0<ρ₀→
    ∃αRef γRich ω pstarRef kstar tstar:ℝ,
      αRef=αHost/2 ∧ 0<αRef ∧ 0<γRich ∧ γRich≤1/2 ∧ γRich≤αRef ∧
      successorCycleRatio k₀+αRef/2≤1/2+αRef ∧
      0<ω ∧ 0<pstarRef ∧ 0<kstar ∧ 0<tstar ∧ tstar≤1/100 ∧ tstar≤1 ∧
      4*ω≤ρ₀ ∧ 4*(m:ℝ)*pstarRef≤ρ₀*(1/100) ∧ tstar=(1/100)/(m:ℝ) ∧
      tstar≤(1/100)/(m:ℝ) ∧
      (∀ρ:ℝ,ρ₀≤ρ→kstar≤ρ*(1/100)/2 ∧ kstar≤ρ*((1/100)/(m:ℝ))/2) ∧
    ∀K d:ℕ,0<K→2≤d→∃BO:Fin K→ℝ,(∀i,0<BO i) ∧
      LongHostMatchingGeometryContinuation m K d αHost A BM BO := by
  obtain ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,hhost⟩:=
    long_host_matching_vortex_geometric_inputs L₀ αHost hα
  refine ⟨m,r,k₀,hm,hLm,heven,hr,hrm,hlen,hmargin,A,BM,hA,hBM,?_⟩
  intro ρ₀ hρ₀
  obtain ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγ,hγ1,hγcap,hmargin',hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound⟩:=
    long_host_adaptive_reference_parameters_exact_tstar m k₀ (by omega) αHost ρ₀ hα hρ₀ hmargin
  refine ⟨αRef,γRich,ω,pstarRef,kstar,tstar,hαRefEq,hαRef,hγ,hγ1,hγcap,hmargin',hω,hp,hk,ht,ht100,ht1,hωb,hpb,htExact,htcap,hkbound,?_⟩
  intro K d hK hd
  obtain ⟨BO,hBO,hcontinue⟩:=hhost K d hK hd
  exact ⟨BO,hBO,hcontinue⟩
end Oberwolfach
