module

public import Oberwolfach.FirstVortexSharedHostVortexTrimDistinctWeights

@[expose] public section
/-! Instantiate the actual host continuation at one tolerance usable by all
three selector branches, producing the vortex, permutation and seed weights
together for the original regular host. -/
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

theorem first_vortex_host_selector_inputs
    (r K d:ℕ) (αRef A BM:ℝ) (BO:Fin K→ℝ)
    (hHost:HostMatchingVortexContinuation (r+4) K d (2*αRef) A BM BO)
    (βQ εQ ρ₀:ℝ) (hβ:0<βQ) (hε:0<εQ) (hε1:εQ<1/4) (hρ:0<ρ₀)
    (mLevel:ℕ) (τ₀ τSeed τOrd:ℝ) (hτ₀:0<τ₀) (hτSeed:0<τSeed) (hτOrd:0<τOrd):
    ∃vsize:ℕ,1≤vsize ∧ mLevel≤vsize ∧
    ∃τ:ℝ,0<τ ∧ τ≤min τ₀ (min τSeed τOrd) ∧
    ∃N:ℕ,1≤N ∧
    ∀Allowed:Set ℕ,Allowed.Nonempty→(∀s∈Allowed,3≤s)→
    ∀n:ℕ,N≤n→
    ∀(U:Type) [Fintype U] (F:U→SimpleGraph (Fin n)) (hF:∀u,(F u).IsRegularOfDegree 2)
      (hAllowed:∀u,AllowedCycleLengths (F u) Allowed)
      (θ:ℝ) (hθ:0<θ) (hθmax:θ≤1/100)
      (hcut:(1/((((r+4):ℕ):ℝ)+1))/(d:ℝ)≤θ)
      (hclass:∀u,factorPreparationClass (F u) K=none)
      (G:SimpleGraph (Fin n)) (D:ℕ) (hreg:G.IsRegularOfDegree D)
      (hmin:(allowedThreshold Allowed+2*αRef)*n≤(D:ℝ))
      (hρlo:ρ₀ ≤ initialIndexDensity U D) (hρhi:initialIndexDensity U D≤1),
    ∃Q:Vortex U G D βQ εQ vsize,∃π:Equiv.Perm (Fin n),
      (∀i x,π x∈Q.extendedVertices i↔x∈Q.extendedVertices i) ∧
      (∀x l,0<l→l<2*d+1→(π^l) x≠x) ∧
      Fintype.card U≤n ∧ 0<D ∧ (0:ℝ)<D ∧ (n:ℝ)/2≤D ∧ (D:ℝ)≤2*n ∧
      (1/2+2*αRef)*n≤(D:ℝ) ∧ initialIndexDensity U D*(D:ℝ)=2*Fintype.card U ∧
      (∀x,|(G.degree x:ℝ)-(D:ℝ)|≤(0:ℝ)*n) ∧ 2*vsize≤n ∧
      Q.length-1+1=Q.length ∧
    ∃w:∀i:Fin K,OrdinaryCycle G (longPaddedSeedExponent i+2)→ℝ,
    ∃wK:(Fin ((r+4)+1)→Fin n)→ℝ,
      (∀i C,0≤w i C) ∧ (∀i C,w i C≤BO i/(n:ℝ)^(longPaddedSeedExponent i)) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,∀x y,
        (∑C,if C.val.val.Adj x y then w i C else 0)=if G.Adj x y then 1 else 0) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,
        6*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))+(0:ℝ)*n≤τ*D) ∧
      (∀i∈longRetainedSeedIndices F hF K θ,
        5*((longPaddedSeedExponent i+2:ℕ):ℝ)^4*BO i*(2*(3*d))/n≤τ) ∧
      SuccessorSequenceWeightConditions G π (3*d) D τ A BM wK :=by
  obtain ⟨vsize,hvsize,hmlevel,hτ⟩:=hHost βQ εQ ρ₀ hβ hε hε1 hρ mLevel
  let τ:=min τ₀ (min τSeed τOrd)/2
  have hτpos:0<τ:=by dsimp [τ];positivity
  have hτbound:τ≤min τ₀ (min τSeed τOrd):=by
    dsimp [τ]
    have hh:0<min τ₀ (min τSeed τOrd):=by positivity
    linarith
  obtain ⟨N,hN,hLate⟩:=hτ τ hτpos
  refine ⟨vsize,hvsize,hmlevel,τ,hτpos,hτbound,max N (2*vsize),?_,?_⟩
  · omega
  · intro Allowed hAllowedNonempty hvalid n hn U _ F hF hAllowed θ hθ hθmax hcut hclass G D hreg hmin hρlo hρhi
    obtain ⟨Q,π,hpres,hnoshort,hU,hD,hDreal,hDlo,hDhi,hmargin,hsize,hdeg,hv,hLen,w,wK,hw,he,hbudget,hwK⟩:=
      hLate Allowed hAllowedNonempty hvalid n hn U F hF hAllowed θ hθ hθmax hcut hclass G D hreg hmin hρlo hρhi
    refine ⟨Q,π,hpres,hnoshort,hU,hD,hDreal,hDlo,hDhi,hmargin,hsize,hdeg,hv,hLen,w,wK,?_,?_,he,?_,?_,hwK⟩
    · intro i C; exact (hw i C).1
    · intro i C; exact (hw i C).2
    · intro i hi; simpa using (hbudget i hi).2
    · intro i hi; exact (hbudget i hi).1
end Oberwolfach
