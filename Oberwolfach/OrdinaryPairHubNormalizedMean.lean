module

public import Oberwolfach.OrdinaryPairHubPatternSpokeMeanExt
public import Oberwolfach.OrdinaryDegreeNormalizedSpokeSeed

@[expose] public section

/-! The exact sampled spoke-root mean, normalized by the fixed sampling
densities, inherits the parent degree and conflict error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_normalized_mean
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ) (hr:2≤r) (hd:2≤d)
    (hn:0<Fintype.card V) (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (weight:OrdinaryCycle P r→ℝ) (hweight:∀ C,0≤weight C)
    (B:ℝ) (hB:0≤B) (hb:∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L:ℝ) (hdeg:∀ v,(F.degree v:ℝ)≤L)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (D ε:ℝ) (hD:0<D) (hnear:∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V)
    (pR:ℝ) (hpR:0<pR) (hpR1:pR≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (u u':U) (hne:u≠u') (hpH:0<s u j*s u' j) (v:V):
    let μ:=rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>hpR1) d hd q hq hQ s hs hS
    let w:=ordinaryCycleWheelWeight (U:=Unit) P F r weight (D/2)
    let c:=pR^r*(s u j*s u' j)^(r-1);
    |(FiniteLaw.pi μ).expectation (fun σ=>
      resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) (Sum.inr (v,()))
        (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u')))/c-1|≤
      (6*(r:ℝ)^4*B*L+ε*Fintype.card V)/D := by
  intro μ w c
  have hc:0<c:=by dsimp [c];positivity
  have hm:=ordinary_pair_hub_pattern_spoke_mean_ext P F π r d (by omega) hd hF hnoshort w pR hpR hpR1
    q hq hQ s hs hS j u u' hne hpH v
  have hseed:=ordinary_degree_normalized_spoke_seed P F r hr hn weight hweight B hB hb L hdeg he D ε hD hnear v
  rw [hm]
  have heq:c*ordinarySpokeLoad w v ()/c=ordinarySpokeLoad w v ():=by field_simp
  rw [heq]
  exact hseed
end Oberwolfach
