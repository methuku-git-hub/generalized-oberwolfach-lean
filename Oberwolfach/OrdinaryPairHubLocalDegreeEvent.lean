module

public import Oberwolfach.OrdinaryPairHubDegreeDefinition

@[expose] public section
/-! The original-law event controls every two-hub local cycle-weighted degree. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 15000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_pair_hub_local_degree_common_event
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
    let C:ℝ:=2*(4*(d:ℝ)+3)
    let err:=(Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((r:ℝ)^4*(4*B)/Fintype.card V)*(2*r)*((r:ℝ)^2*(4*B)))));
    1-(Fintype.card (U×U):ℝ)*err≤μ.probability (fun σ=>∀ u u',u≠u'→∀ v,
      let c:=pR^r*(s u j*s u' j)^(r-1);
      ordinaryPairHubSpokes π d σ j u u' v () →
      |1-ordinaryPairHubLocalDegree P F π d σ j u u' weight D c v|≤
          t/c+(6*(r:ℝ)^4*B*L+ε*Fintype.card V)/D) := by
  intro μ C err
  have hgood:=ordinary_pair_hub_normalized_load_common_event P F π r d hr hd hn hF hnoshort weight hweight B hB hb L hdeg he D ε hD hnear pR hpR hpR1 q hq hQ s hs hS j hsp t ht
  apply hgood.trans
  apply finiteLaw_probability_mono
  intro σ hσ u u' hne v c hv
  have hid:=ordinary_pair_hub_named_local_degree_identity P F π d σ j u u' weight D c v hv
  rw [hid,abs_sub_comm]
  convert hσ u u' hne v using 1 <;> congr!
end Oberwolfach
