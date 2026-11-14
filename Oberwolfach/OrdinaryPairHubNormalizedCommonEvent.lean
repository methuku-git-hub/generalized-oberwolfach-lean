module

public import Oberwolfach.OrdinaryPairHubSeedPatternConcentration
public import Oberwolfach.OrdinaryPairHubNormalizedMean

@[expose] public section

/-! One original-law event controls all normalized two-hub spoke-root
loads of the degree-normalized parent cycle seed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_pair_hub_normalized_load_common_event
    (P F:SimpleGraph V) (π:Equiv.Perm V) (r d:ℕ) (hr:2≤r) (hd:2≤d)
    (hn:0<Fintype.card V) (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (weight:OrdinaryCycle P r→ℝ) (hweight:∀ C,0≤weight C)
    (B:ℝ) (hB:0<B) (hb:∀ C,weight C≤B/(Fintype.card V:ℝ)^(r-2))
    (L:ℝ) (hdeg:∀ v,(F.degree v:ℝ)≤L)
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (D ε:ℝ) (hD:(Fintype.card V:ℝ)/2≤D) (hnear:∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V)
    (pR:ℝ) (hpR:0<pR) (hpR1:pR≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (hsp:∀ u,0<s u j) (t:ℝ) (ht:0<t):
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>pR) (fun _=>hpR.le) (fun _=>hpR1) d hd q hq hQ s hs hS)
    let w:=ordinaryCycleWheelWeight (U:=Unit) P F r weight (D/2)
    let C:ℝ:=2*(4*(d:ℝ)+3)
    let err:=(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((r:ℝ)^4*(4*B)/Fintype.card V)*(2*r)*((r:ℝ)^2*(4*B)))));
    1-(Fintype.card (U×U):ℝ)*err≤μ.probability (fun σ=>∀ u u',u≠u'→∀ v,
      let c:=pR^r*(s u j*s u' j)^(r-1);
      |resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) (Sum.inr (v,()))
        (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u'))/c-1|≤
          t/c+(6*(r:ℝ)^4*B*L+ε*Fintype.card V)/D) := by
  intro μ w C err
  have hconc:=ordinary_pair_hub_seed_pattern_concentration P F π r d hr hd hn weight hweight B hB hb D hD
    (fun _=>pR) (fun _=>hpR.le) (fun _=>hpR1) q hq hQ s hs hS j t ht
  apply hconc.trans
  apply finiteLaw_probability_mono
  intro σ hgood u u' hne v c
  have hn0:(0:ℝ)<Fintype.card V:=by exact_mod_cast hn
  have hD0:0<D:=by linarith
  have hpH:0<s u j*s u' j:=mul_pos (hsp u) (hsp u')
  have hc:0<c:=by dsimp [c];positivity
  let X:=resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) (Sum.inr (v,()))
    (ordinaryResourceState (rawWheelGraph P σ) (ordinaryPairHubSpokes π d σ j u u'))
  let M:=μ.expectation (fun τ=>resourcePatternLoad ordinaryWheelResources w (fun _ _=>true) (Sum.inr (v,()))
    (ordinaryResourceState (rawWheelGraph P τ) (ordinaryPairHubSpokes π d τ j u u')))
  have hdiff:|X-M|≤t:=(hgood u u' (Sum.inr (v,()))).le
  have hmean:=ordinary_pair_hub_normalized_mean P F π r d hr hd hn hF hnoshort weight hweight B hB.le hb L hdeg he D ε hD0 hnear
    pR hpR hpR1 q hq hQ s hs hS j u u' hne hpH v
  have hdiff':|(X-M)/c|≤t/c:=by
    rw [abs_div,abs_of_pos hc]
    exact div_le_div_of_nonneg_right hdiff hc.le
  have heq:X/c-1=(X-M)/c+(M/c-1):=by ring
  change |X/c-1|≤_
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hdiff' hmean)
end Oberwolfach
