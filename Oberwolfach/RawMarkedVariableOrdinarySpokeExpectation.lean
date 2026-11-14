module

public import Oberwolfach.RawMarkedSeedVariableExpectation

@[expose] public section
/-! At an ordinary-spoke root the marked probability of that same hub
remains in the numerator; it may be zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem rawMarkedSeed_variable_ordinary_spoke_expectation
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0<k) (hsum:2*p+2*k≤1)
    (d:ℕ) (hd:2≤d)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j) (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g))
    (hnoshort:∀ x l,0<l→l<2*d+1→(π^l) x≠x)
    (m:ℕ) (hm:2≤m) (H₀ Hₖ:V→U→Prop)
    (g:Γ) (j:Color) (D:ℝ) (hD:0<D) (hspos:∀ u,0<s u j)
    (weight:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hsupport:∀ W,weight W≠0→
      (∀ i:Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
      P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (x:V) (u:U):
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk.le hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad (fun W=>weight W/(D*p^m*k*(s W.2.val j)^m))
        (rawMarkedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr (false,x,u)))=
      ∑ W,if Sum.inr (false,x,u)∈typedMarkedOccurrenceResources W then weight W*q u g/(D*s u j) else 0 := by
  have hroot:rawMarkedWheelMarginal P π d p k q s g j (Sum.inr (false,x,u))≠0:=by
    simpa [rawMarkedWheelMarginal] using (ne_of_gt (hspos u))
  rw [rawMarkedSeed_variable_hub_expectation P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ g j D hD hspos weight hsupport (Sum.inr (false,x,u)) hroot]
  apply Finset.sum_congr rfl
  intro W _
  split_ifs with hW
  · obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W (false,x,u)).mp hW
    have hu:W.2.val=u:=by
      have hh:=congrArg (fun z:Bool×V×U=>z.2.2) hi
      simpa using hh
    simp only [rawMarkedWheelMarginal,Bool.false_eq_true,ite_false]
    rw [hu]
  · rfl
end Oberwolfach
