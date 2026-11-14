module

public import Oberwolfach.OrdinaryPairHubPatternMarginalExpectation
public import Oberwolfach.OrdinaryRawMeanFactors

@[expose] public section

/-! Exact omitted-spoke-root mean on the common class of two distinct hubs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_marginal_on_candidate_ext
    (P F:SimpleGraph V) (r:ℕ) (s:U→Color→ℝ) (j:Color) (u u':U) (pR:ℝ)
    (W:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r) (a:Sym2 V⊕(V×Unit))
    (ha:a∈ordinaryWheelResources W):
    ordinaryPairHubMarginal P (fun _=>pR) s j u u' a=
      Sum.elim (fun _=>pR) (fun _=>s u j*s u' j) a := by
  cases a with
  | inl e=>
    have he:e∈P.edgeSet:=by
      rw [ordinaryWheelResources_rim] at ha
      induction e using Sym2.ind with
      | _ x y=>exact W.val.1.property ha
    simp only [ordinaryPairHubMarginal,he,ite_true,Sum.elim_inl]
  | inr a=>rfl

theorem ordinary_pair_hub_pattern_spoke_mean_ext
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ) (hr:1≤r) (hd:2≤d)
    (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (w:OrdinaryWheel P F (fun (_:V) (_:Unit)=>True) r→ℝ)
    (pR:ℝ) (hpR:0<pR) (hpR1:pR≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (u u':U) (hne:u≠u') (hpH:0<s u j*s u' j) (v:V):
    let μ:=rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>hpR1) d hd q hq hQ s hs hS;
    (FiniteLaw.pi μ).expectation (fun σ=>
      resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) (Sum.inr (v,()))
        (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u')))=
      pR^r*(s u j*s u' j)^(r-1)*ordinarySpokeLoad w v () := by
  intro μ
  rw [ordinary_pair_hub_pattern_marginal_expectation P F π r d hd hF hnoshort w (fun _=>pR) (fun _=>hpR.le) (fun _=>hpR1)
    q hq hQ s hs hS j u u' hne (Sum.inr (v,()))]
  unfold ordinarySpokeLoad
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · ext W; simp
  · intro W _
    by_cases he:Sum.inr (v,())∈ordinaryWheelResources W
    · have hvu:=(ordinaryWheelResources_spoke W v ()).mp he
      rw [if_pos he,if_pos hvu]
      have hh:=Finset.prod_congr rfl (fun a (ha:a∈ordinaryWheelResources W\{Sum.inr (v,())})=>
        ordinary_pair_hub_marginal_on_candidate_ext P F r s j u u' pR W a (Finset.mem_sdiff.mp ha).1)
      rw [hh,ordinaryWheelResources_spoke_omitted_product W hr pR (s u j*s u' j) hpH.ne' _ he]
      ring
    · have hvu:¬(ordinaryWheelHub W=() ∧ v∈(ordinaryWheelRim W).support):=
        fun h=>he ((ordinaryWheelResources_spoke W v ()).mpr h)
      have hv:v∉(ordinaryWheelRim W).support:=by
        intro hh
        exact hvu ⟨Subsingleton.elim _ _,hh⟩
      simp [he,hv]
end Oberwolfach
