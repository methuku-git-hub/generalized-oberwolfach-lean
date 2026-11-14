module

public import Oberwolfach.OrdinaryShiftedSeedExpectation

@[expose] public section
/-! For a marked-spoke root the root marginal cancels locally, without
requiring positive marked probabilities at any other hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem ordinary_shifted_interval_spoke_expectation
    (P:SimpleGraph V) (π:Equiv.Perm V)
    (p k:ℝ) (hp:0<p) (hk:0≤k) (hsum:2*p+2*k≤1)
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
    (x:V) (u:U) (hqu:q u g≠0):
    (FiniteLaw.pi (rawMarkedWheelLaw p k hp.le hk hsum d hd q hq hQ s hs hS)).expectation
      (fun σ=>typedMarkedPotentialLoad (fun W=>weight W/(D*p^(m+1)*(s W.2.val j)^m))
        (ordinaryShiftedPairRims P π d σ) (rawMarkedPairSpokes π d σ g j) (Sum.inr (true,x,u)))=
      ∑ W,if Sum.inr (true,x,u)∈typedMarkedOccurrenceResources W then weight W/D else 0 := by
  have hroot:rawMarkedWheelMarginal P π d p p q s g j (Sum.inr (true,x,u))≠0:=by
    simpa [rawMarkedWheelMarginal] using hqu
  rw [ordinary_shifted_seed_expectation P π p k hp hk hsum d hd q hq hQ s hs hS
    hnoshort m hm H₀ Hₖ g j D hD hspos weight hsupport (Sum.inr (true,x,u)) hroot]
  apply Finset.sum_congr rfl
  intro W _
  split_ifs with hW
  · obtain ⟨i,hi⟩:=(typedMarkedOccurrenceResources_spoke W (true,x,u)).mp hW
    have hu:W.2.val=u:=by
      have hh:=congrArg (fun z:Bool×V×U=>z.2.2) hi
      simpa using hh
    simp only [rawMarkedWheelMarginal,Bool.true_eq_false,ite_true]
    rw [hu]
    field_simp
  · rfl
end Oberwolfach
