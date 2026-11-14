module

public import Oberwolfach.RawMarkedSeedProducts

@[expose] public section

/-! Exact root-omitted means for the fixed normalized seed. The support
condition names the actual parent edges, rather than a surrogate event. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarkedSeed_expectation
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0<p) (hk : 0<k) (hsum : 2*p+2*k≤1)
    (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u g,0≤q u g) (hQ : ∀ u,∑ g,q u g≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (m : ℕ) (hm : 2≤m) (H₀ Hₖ : V→U→Prop)
    (g : Γ) (j : Color) (s₀ t₀ D : ℝ) (hs₀ : 0<s₀) (hD : 0<D)
    (hq₀ : ∀ u,q u g=t₀) (hs₀' : ∀ u,s u j=s₀)
    (weight : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hsupport : ∀ W,weight W≠0 →
      (∀ i : Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
      P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (root : ((V×V)⊕(V×V))⊕(Bool×V×U))
    (hroot : rawMarkedWheelMarginal P π d p k q s g j root≠0) :
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad (fun W=>weight W/(D*p^m*k*s₀^m))
        (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root)=
      (t₀/(D*rawMarkedWheelMarginal P π d p k q s g j root))*
        ∑ W,if root∈typedMarkedOccurrenceResources W then weight W else 0 := by
  rw [rawMarkedPotentialLoad_expectation P π p k hp.le hk.le hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ (fun W=>weight W/(D*p^m*k*s₀^m)) g j root,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  letI : DecidableEq V := Classical.decEq _
  by_cases hW : root∈typedMarkedOccurrenceResources W
  · simp only [hW,ite_true]
    by_cases hw : weight W=0
    · simp only [hw,zero_div,zero_mul,mul_zero]
    · have hh := rawMarkedSeed_candidate_mean P (by omega) W p k s₀ t₀ D (weight W)
        hp.ne' hk.ne' hs₀.ne' hD.ne' q s g j hq₀ hs₀' (hsupport W hw).1 (hsupport W hw).2 root hW hroot
      convert hh using 1 <;> ring
  · simp only [hW,ite_false,zero_mul,mul_zero]

end Oberwolfach
