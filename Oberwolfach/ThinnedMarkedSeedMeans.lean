module

public import Oberwolfach.ThinnedMarkedSampling
public import Oberwolfach.RawMarkedSeedProducts
public import Oberwolfach.MarkedSeedMeanBounds

@[expose] public section

/-! The common-cycle seed uses the same parent weighting for every hub pair.
Both root spokes and the root coin are omitted. Its expectation is the
parent positional mass divided by the original degree centre, not an
assumed exact unit mass. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option quotPrecheck false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color : Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [LinearOrder V] [DecidableEq U]

theorem thinnedMarkedSeed_expectation
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U) (hu : u≠u')
    (m : ℕ) (hm : 2≤m) (H₀ Hₖ : V→Unit→Prop)
    (sbar tbar D : ℝ) (hsbar : 0<sbar) (hD : 0<D)
    (hqbar : q u g*q u' g=tbar) (hsbar' : s u j*s u' j*θ=sbar)
    (weight : MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d) H₀ Hₖ→ℝ)
    (hsupport : ∀ W,weight W≠0 →
      (∀ i : Fin m,P.Adj (W.1.val i.castSucc) (W.1.val i.succ)) ∧
      P.Adj (W.1.val (Fin.last m)) (π (W.1.val 0)))
    (root : ((V×V)⊕(V×V))⊕(Bool×V×Unit))
    (hroot : rawMarkedWheelMarginal P π d p k
      (fun (_ : Unit) a=>q u a*q u' a) (fun (_ : Unit) j=>s u j*s u' j*θ) g j root≠0) :
    (FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS) θ hθ hθ1)).expectation
      (fun σ=>typedMarkedPotentialLoad (fun W=>weight W/(D*p^m*k*sbar^m))
        (rawMarkedPairRims P π d (fun e=>σ (Sum.inl e))) (thinnedMarkedSpokes π d g j u u' σ) root)=
      (tbar/(D*rawMarkedWheelMarginal P π d p k
        (fun (_ : Unit) a=>q u a*q u' a) (fun (_ : Unit) j=>s u j*s u' j*θ) g j root))*
        ∑ W,if root∈typedMarkedOccurrenceResources W then weight W else 0 := by
  rw [thinnedMarkedPotentialLoad_expectation P π p k hp.le hk.le hphys d hd q hq hQ s hs hS θ hθ hθ1 g j u u'
    hnoshort hu m hm H₀ Hₖ (fun W=>weight W/(D*p^m*k*sbar^m)) root,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro W _
  letI : DecidableEq V := Classical.decEq _
  by_cases hW : root∈typedMarkedOccurrenceResources W
  · simp only [hW,ite_true]
    by_cases hw : weight W=0
    · simp only [hw,zero_div,zero_mul,mul_zero]
    · have hh := rawMarkedSeed_candidate_mean P (by omega) W p k sbar tbar D (weight W)
        hp.ne' hk.ne' hsbar.ne' hD.ne' (fun (_ : Unit) a=>q u a*q u' a)
        (fun (_ : Unit) j=>s u j*s u' j*θ) g j (fun _=>hqbar) (fun _=>hsbar')
        (hsupport W hw).1 (hsupport W hw).2 root hW hroot
      convert hh using 1 <;> ring
  · simp only [hW,ite_false,zero_mul,mul_zero]

theorem thinnedMarkedSeed_spoke_mean
    (P : SimpleGraph V) (π : Equiv.Perm V)
    (p k : ℝ) (hp : 0<p) (hk : 0<k) (hphys : 2*p+2*k≤1) (d : ℕ) (hd : 2≤d)
    (q : U→Γ→ℝ) (hq : ∀ u a,0≤q u a) (hQ : ∀ u,∑ a,q u a≤1/8)
    (s : U→Color→ℝ) (hs : ∀ u j,0≤s u j)
    (hS : ∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ a,q u a))
    (hnoshort : ∀ x l,0<l → l<2*d+1 → (π^l) x≠x)
    (θ : ℝ) (hθ : 0≤θ) (hθ1 : θ≤1) (g : Γ) (j : Color) (u u' : U) (hu : u≠u')
    (m : ℕ) (hm : 2≤m) (sbar tbar D τ A B : ℝ) (hsbar : 0<sbar) (hD : 0<D)
    (hqbar : q u g*q u' g=tbar) (hsbar' : s u j*s u' j*θ=sbar) (ht : tbar=sbar/m)
    (weight : (Fin (m+1)→V)→ℝ)
    (hw : SuccessorSequenceWeightConditions P π (3*d) D τ A B weight) (b : Bool) (v : V) :
    let Parent := MarkedWheel (Prod.fst : V×V→V) Prod.snd Prod.fst Prod.snd m π (3*d)
      (fun (_ : V) (_ : Unit)=>True) (fun _ _=>True)
    |(FiniteLaw.pi (thinnedMarkedLaw (rawMarkedWheelLaw p k hp.le hk.le hphys d hd q hq hQ s hs hS) θ hθ hθ1)).expectation
      (fun σ=>typedMarkedPotentialLoad (fun W : Parent=>weight W.1.val/(D*p^m*k*sbar^m))
        (rawMarkedPairRims P π d (fun e=>σ (Sum.inl e))) (thinnedMarkedSpokes π d g j u u' σ) (Sum.inr (b,v,())))-1|≤τ := by
  dsimp only
  have htbar : 0<tbar := by rw [ht];positivity
  have hroot : rawMarkedWheelMarginal P π d p k
      (fun (_ : Unit) a=>q u a*q u' a) (fun (_ : Unit) j=>s u j*s u' j*θ) g j (Sum.inr (b,v,()))≠0 := by
    cases b <;> simp only [rawMarkedWheelMarginal,hqbar,hsbar',Bool.false_eq_true,ite_true,ite_false] <;> positivity
  rw [thinnedMarkedSeed_expectation P π p k hp hk hphys d hd q hq hQ s hs hS hnoshort
    θ hθ hθ1 g j u u' hu m hm (fun _ _=>True) (fun _ _=>True) sbar tbar D hsbar hD hqbar hsbar'
    (fun W=>weight W.1.val) (fun W hW=>successor_weight_parent_edges hw W.1.val hW) (Sum.inr (b,v,())) hroot]
  simpa only [rawMarkedWheelMarginal,hqbar,hsbar'] using
    markedParent_spoke_normalized hw (by omega) hD sbar tbar hsbar ht b v ()

theorem commonThinning_parameters (m : ℕ) (hm : 1≤m) (s : ℝ) (hs : 0<s) :
    0≤1/(m:ℝ) ∧ 1/(m:ℝ)≤1 ∧ 0<s*s/m ∧
      (s/m)*(s/m)=(s*s/m)/m ∧ s*s*(1/(m:ℝ))=s*s/m := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (0:ℝ)<m := by linarith
  refine ⟨by positivity,(div_le_iff₀ hm0).mpr (by simpa),by positivity,?_,?_⟩
  · field_simp
  · ring

end Oberwolfach
