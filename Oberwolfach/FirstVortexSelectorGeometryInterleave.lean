module

public import Oberwolfach.FirstVortexHostGeometrySelectorInputs

@[expose] public section
/-! Keep the selector's late result and the host geometry continuation at
one vortex parameter, with the level size chosen after that parameter. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 65536
set_option maxRecDepth 32768
set_option maxHeartbeats 120000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
attribute [local instance] referenceWitnessFinDecidable
attribute [local instance 100000] Finset.decidableDforallFinset

def FirstVortexGeometryHostFamily
    (r K d:ℕ) (αRef ρ₀ ε κ hcut ξ xiDeep ω x:ℝ) (N NI:ℕ)
    (A BM:ℝ) (BO:Fin K→ℝ) (β:ℝ) (mGeom mLevel:ℕ) (τ₀ τSeed τOrd:ℝ):Prop :=
    ∃vsize:ℕ,1≤vsize ∧ mLevel≤vsize ∧ mGeom≤vsize ∧
    ∃τ:ℝ,0<τ ∧ τ≤min τ₀ (min τSeed τOrd) ∧
    ∃NHost:ℕ,1≤NHost ∧
    ∀Allowed:Set ℕ,Allowed.Nonempty→(∀s∈Allowed,3≤s)→
    ∀n:ℕ,NHost≤n→
    ∀(U:Type) [Fintype U] [DecidableEq U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
      (hcutHost:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
      (hclass:∀u,factorPreparationClass (F u) K=none)
      (G:SimpleGraph (Fin n)) (D:ℕ) (hreg:G.IsRegularOfDegree D)
      (hmin:(allowedThreshold Allowed+2*αRef)*n≤(D:ℝ))
      (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    ∃Q:Vortex U G D β ε vsize,∃π:Equiv.Perm (Fin n),
      (∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) ∧
      (∀x l,0<l→l<2*d+1→(π^l) x≠x) ∧
      Fintype.card U≤n ∧ 0<D ∧ (0:ℝ)<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧
      (1/2+2*αRef)*n≤(D:ℝ) ∧ initialIndexDensity U D*(D:ℝ)=2*Fintype.card U ∧
      (∀x,|(G.degree x:ℝ)-(D:ℝ)|≤(0:ℝ)*n) ∧ 2*vsize≤n ∧ Q.length-1+1=Q.length ∧
      (∀L:ℕ,L<Q.length→MarkedVortexGeometricRecordEvent Q αRef ρ₀ κ hcut ξ xiDeep ω x N NI L) ∧
    ∃w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ,
    ∃wK:(Fin ((r+4)+1)→Fin n)→ℝ,
      (∀i C,0≤w i C) ∧ (∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀v z,
        (∑C,if C.val.val.Adj v z then w i C else 0)=if G.Adj v z then 1 else 0) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,
        6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+(0:ℝ)*n≤τ*D) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,
        5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BM wK

/-- Interleave the selector's β-dependent level choice and the actual host
construction. `Late` can be the selector's entire remaining continuation. -/
theorem first_vortex_selector_geometry_interleave
    (r K d:ℕ) (αRef ρ₀ ε κ hcut ξ xiDeep ω x βmax εBal εRef:ℝ) (N NI:ℕ)
    (hN:1≤N) (hα:0<αRef) (hρ₀:0<ρ₀) (he:0<ε) (he8:ε≤1/8) (heAlpha:ε≤αRef/8)
    (hκ:0<κ) (heκ:ε≤κ) (hecut:ε≤hcut) (heξ:4*ε≤ξ) (hedeep:ε^2≤xiDeep)
    (hω:0≤ω) (hωv:ω≤ε/8) (hωu:ω≤ρ₀*ε/64)
    (hx:0<x) (hβ:0<βmax) (hBal:0<εBal) (hRef:0<εRef)
    (A BM:ℝ) (BO:Fin K→ℝ)
    (hHost:HostMatchingVortexContinuation (r+4) K d (2*αRef) A BM BO)
    (τSeed τOrd:ℝ) (hτSeed:0<τSeed) (hτOrd:0<τOrd)
    (Late:ℝ→ℕ→ℝ→Prop)
    (hSelect:∀β:ℝ,0≤β→β≤1/4→β≤αRef/4→β≤βmax→β≤εBal/4→β≤εRef/4→
      ∃mLevel:ℕ,∃τ₀:ℝ,0<τ₀ ∧ Late β mLevel τ₀):
    ∃β:ℝ,0<β ∧ β≤1/4 ∧ β≤αRef/4 ∧ β≤βmax ∧ β≤εBal/4 ∧ β≤εRef/4 ∧
    ∃mGeom mLevel:ℕ,1≤mGeom ∧ ∃τ₀:ℝ,0<τ₀ ∧ Late β mLevel τ₀ ∧
      FirstVortexGeometryHostFamily r K d αRef ρ₀ ε κ hcut ξ xiDeep ω x N NI A BM BO β mGeom mLevel τ₀ τSeed τOrd :=by
  obtain ⟨β,hβ0,hβquarter,hβα,hβαstrong,hβstrong,hβκ,hβx,hβmax,hβbal,hβref,mGeom,hmGeom,hHostFuture⟩:=
    first_vortex_host_geometry_selector_inputs r K d αRef ρ₀ ε κ hcut ξ xiDeep ω x βmax εBal εRef N NI
      hN hα hρ₀ he he8 heAlpha hκ heκ hecut heξ hedeep hω hωv hωu hx hβ hBal hRef A BM BO hHost
  have hβα4:β≤αRef/4:=by linarith
  obtain ⟨mLevel,τ₀,hτ₀,hLate⟩:=hSelect β hβ0.le hβquarter hβα4 hβmax hβbal hβref
  refine ⟨β,hβ0,hβquarter,hβα4,hβmax,hβbal,hβref,mGeom,mLevel,hmGeom,τ₀,hτ₀,hLate,?_⟩
  exact hHostFuture mLevel τ₀ τSeed τOrd hτ₀ hτSeed hτOrd
end Oberwolfach
