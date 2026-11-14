module

public import Oberwolfach.OrdinaryShiftedMarkedPotentialSampling
public import Oberwolfach.RawMarkedSeedVariableHub

@[expose] public section
/-! Exact root-omitted expectation for the ordinary shifted candidate seed,
with the same physical rim probability at every position. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_seed_expectation
    (P:SimpleGraph V) (π:Equiv.Perm V) (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d) (q:U→Γ→ℝ) (hq:∀u g,0≤q u g) (hQ:∀u,∑g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀u j,0≤s u j) (hS:∀u,∑j,s u j ≤ intervalUncoveredProbability d (∑g,q u g))
    (hnoshort:∀x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (H₀ Hₖ:V→U→Prop) (g:Γ) (j:Color)
    (D:ℝ) (hD:0<D) (hspos:∀u,0<s u j)
    (weight:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hsupport:∀W,weight W≠0→
      (∀i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
      P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (root:((V×V)⊕(V×V))⊕(Bool×V×U))
    (hroot:rawMarkedWheelMarginal P π d p p q s g j root≠0):
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad
        (fun W=>weight W/(D*p^(m+1)*(s W.2.val j)^m))
        (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) root)=
      ∑W,if root∈typedMarkedOccurrenceResources W then
        weight W*q W.2.val g/(D*rawMarkedWheelMarginal P π d p p q s g j root) else 0 :=by
  rw [ordinary_shifted_potential_expectation P π p k hp.le hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ (fun W=>weight W/(D*p^(m+1)*(s W.2.val j)^m)) g j root]
  apply Finset.sum_congr rfl
  intro W _
  letI : DecidableEq V := Classical.decEq _
  by_cases hW:root∈typedMarkedOccurrenceResources W
  · simp only [hW,ite_true]
    by_cases hw:weight W=0
    · simp [hw]
    · have hh:=rawMarkedSeed_candidate_variable_hub_mean P (by omega) W p p D (weight W)
        hp.ne' hp.ne' hD.ne' q s g j (ne_of_gt (hspos W.2.val))
        (hsupport W hw).1 (hsupport W hw).2 root hW hroot
      simpa only [pow_succ,mul_assoc] using hh
  · simp [hW]
end Oberwolfach
