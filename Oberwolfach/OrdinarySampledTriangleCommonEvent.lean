module

public import Oberwolfach.OrdinarySampledTriangleProfileProperty
public import Oberwolfach.OrdinaryPairHubLocalDegreeEvent
public import Oberwolfach.RawOrdinaryRowEvent
public import Oberwolfach.GoodPlacementEvents

@[expose] public section
/-! One original-law event supplies all triangular two-hub profile inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
theorem ordinary_sampled_triangle_property_common_event
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (hd:2≤d)
    (hn:0<Fintype.card V) (hF:permutationConflictGraph π (3*d)≤F)
    (hnoshort:∀ x k,0<k→k<2*d+1→(π^k) x≠x)
    (weight:OrdinaryCycle P 3→ℝ) (hweight:∀ C,0≤weight C)
    (a b:ℝ) (ha:0≤a) (hb:0<b)
    (hwlo:∀ C,a/(Fintype.card V:ℝ)≤weight C)
    (hwhi:∀ C,weight C≤b/(Fintype.card V:ℝ))
    (L α:ℝ) (hL:0≤L) (hα:0<α) (hdeg:∀ v,(F.degree v:ℝ)≤L)
    (hP:∀ v,(3/4+α)*Fintype.card V≤(P.degree v:ℝ))
    (he:∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0)
    (D ε:ℝ) (hD:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (hnear:∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V)
    (p pmin smin:ℝ) (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1) (hsmin:0<smin) (hsmin1:smin≤1)
    (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
    (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
    (hS:∀ u,∑ j,s u j ≤ intervalUncoveredProbability d (∑ g,q u g))
    (j:Color) (hslo:∀ u,smin≤s u j) (hshi:∀ u,s u j≤1)
    (t trow β η:ℝ) (ht:0<t) (htrow:0<trow)
    (hmargin:β*Fintype.card V≤(pmin^4*smin^4)*(4*(min α (1/4)))*Fintype.card V-trow-4*L)
    (herr:t/(pmin^3*(smin*smin)^2)+(6*(3:ℝ)^4*b*L+ε*Fintype.card V)/D≤η):
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>le_trans hpmin.le hp) (fun _=>hp1) d hd q hq hQ s hs hS)
    let C:ℝ:=2*(4*(d:ℝ)+3)
    let errD:=(Fintype.card (U×U):ℝ)*((Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((3:ℝ)^4*(4*b)/Fintype.card V)*(2*3)*((3:ℝ)^2*(4*b))))))
    let errR:=(Fintype.card V+1:ℝ)^4*(Fintype.card U+1:ℝ)^4*
      (2*Real.exp (-2*trow^2/((4*(d:ℝ)+3)^2*(2*(2*(4:ℝ)+1)*Fintype.card V))));
    1-errD-errR≤μ.probability (ordinarySampledTriangleProfileProperty P F π d · pmin smin j β η a b) := by
  intro μ C errD errR
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn
  have hp0:0<p:=lt_of_lt_of_le hpmin hp
  have hsp:∀ u,0<s u j:=fun u=>lt_of_lt_of_le hsmin (hslo u)
  have hA:(Finset.univ:Finset V).Nonempty:=Finset.card_pos.mp (by simpa using hn)
  let E:=fun (σ:RawWheelOutcome V U Γ Color)=>∀ u u',u≠u'→∀ v,
    let c:=p^3*(s u j*s u' j)^2;
    ordinaryPairHubSpokes π d σ j u u' v () →
      |1-ordinaryPairHubLocalDegree P F π d σ j u u' weight D c v|≤
        t/c+(6*(3:ℝ)^4*b*L+ε*Fintype.card V)/D
  let R:RawWheelOutcome V U Γ Color→Prop:=RawOrdinaryRows P π d 4 Finset.univ p s j trow
  have hE:1-errD≤μ.probability E:=by
    have hh:=ordinary_pair_hub_local_degree_common_event P F π 3 d (by norm_num) hd hn hF hnoshort weight hweight b hb (by simpa using hwhi) L hdeg he D ε hD hnear p hp0 hp1 q hq hQ s hs hS j hsp t ht
    simpa only [E,errD,C,Nat.reduceSub,Nat.cast_ofNat] using hh
  have hR:1-errR≤μ.probability R:=by
    have hh:=rawOrdinaryRows_common_event P π d hd p hp0.le hp1 q hq hQ s hs hS hnoshort Finset.univ hA 4 j trow htrow
    simp only [Finset.card_univ] at hh
    convert hh using 1 <;> try ring <;> congr!
  have hjoint:=finiteLaw_good_intersection μ E R errR hR
  have hprob:1-errD-errR≤μ.probability (fun σ=>E σ∧R σ):=by linarith only [hE,hjoint]
  apply hprob.trans
  apply finiteLaw_probability_mono
  intro σ hσ
  apply ordinary_sampled_triangle_property_from_inputs P F π d σ p pmin smin s j α trow L β η a b D
    hnR hα hL hP hdeg hpmin hp hp1 hsmin hsmin1 hslo hshi ha hb.le hD hDhi weight hwlo hwhi hσ.2 hmargin
  intro u u' hne v hv
  have hpair:=pair_hub_density_bounds 3 p pmin (s u j) (s u' j) smin hpmin hp hp1 hsmin (hslo u) (hslo u') (hshi u) (hshi u')
  have hdiv:t/(p^3*(s u j*s u' j)^2)≤t/(pmin^3*(smin*smin)^2):=
    div_le_div_of_nonneg_left ht.le hpair.1 hpair.2.1
  exact (hσ.1 u u' hne v hv).trans (by linarith only [hdiv,herr])
end Oberwolfach
