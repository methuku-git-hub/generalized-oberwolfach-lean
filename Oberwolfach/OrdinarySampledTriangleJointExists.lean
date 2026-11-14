module

public import Oberwolfach.OrdinarySampledTriangleCommonEvent
public import Oberwolfach.OrdinaryTriangleProfileErrorBound
public import Oberwolfach.OrdinaryProfileEventExists

@[expose] public section
/-! An actual original-law outcome supplies the triangular profile inputs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 20000000
set_option synthInstance.maxSize 32768
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_sampled_triangle_property_joint_exists
    (d:ℕ) (hd:2≤d) (b t ρ:ℝ) (hb:0<b) (ht:0<t) (hρ:0<ρ):
    ∃ N:ℕ,∀ (V U Γ Color:Type) [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
      [DecidableEq V] [DecidableEq U],
    N≤Fintype.card V → Fintype.card U≤Fintype.card V →
    ∀ (P F:SimpleGraph V) (π:Equiv.Perm V),
    permutationConflictGraph π (3*d)≤F →
    (∀ x k,0<k→k<2*d+1→(π^k) x≠x) →
    ∀ weight:OrdinaryCycle P 3→ℝ,(∀ C,0≤weight C) →
    ∀ a:ℝ,0≤a → (∀ C,a/(Fintype.card V:ℝ)≤weight C) →
    (∀ C,weight C≤b/(Fintype.card V:ℝ)) →
    ∀ L α:ℝ,0≤L → 0<α → (∀ v,(F.degree v:ℝ)≤L) →
    (∀ v,(3/4+α)*Fintype.card V≤(P.degree v:ℝ)) →
    (∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if P.Adj x y then 1 else 0) →
    ∀ D ε:ℝ,(Fintype.card V:ℝ)/2≤D → D≤2*Fintype.card V →
    (∀ v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V) →
    ∀ (p pmin smin:ℝ) (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1), 0<smin → smin≤1 →
    ∀ (q:U→Γ→ℝ) (hq:∀ u g,0≤q u g) (hQ:∀ u,∑ g,q u g≤1/8)
      (s:U→Color→ℝ) (hs:∀ u j,0≤s u j)
      (hS:∀ u,∑ j,s u j≤ intervalUncoveredProbability d (∑ g,q u g)) (j:Color),
    (∀ u,smin≤s u j) → (∀ u,s u j≤1) → ∀ β η:ℝ,
    β*Fintype.card V≤(pmin^4*smin^4)*(4*(min α (1/4)))*Fintype.card V-ρ*Fintype.card V-4*L →
    t/(pmin^3*(smin*smin)^2)+(6*(3:ℝ)^4*b*L+ε*Fintype.card V)/D≤η →
    let μ:=FiniteLaw.pi (rawWheelLaw (fun _ : Sym2 V=>p) (fun _=>le_trans (le_of_lt hpmin) hp) (fun _=>hp1) d hd q hq hQ s hs hS);
    ∀ E:RawWheelOutcome V U Γ Color→Prop,
    2/(Fintype.card V:ℝ)^2 < μ.probability E →
    ∃ σ:RawWheelOutcome V U Γ Color,
      E σ ∧ ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b := by
  obtain ⟨N,hN⟩:=ordinary_triangle_profile_error_bound d b t ρ hb ht hρ
  refine ⟨max 2 N,?_⟩
  intro V U Γ Color _ _ _ _ _ _ hn hu P F π hF hnoshort weight hweight a ha hwlo hwhi L α hL hα hdeg hP he D ε hD hDhi hnear p pmin smin hpmin hp hp1 hsmin hsmin1 q hq hQ s hs hS j hslo hshi β η hmargin herr μ E hE
  have hn2:2≤Fintype.card V:=by omega
  have hn0:0<Fintype.card V:=by omega
  have hnR:0<(Fintype.card V:ℝ):=by exact_mod_cast hn0
  have hp0:0<p:=lt_of_lt_of_le hpmin hp
  let C:ℝ:=2*(4*(d:ℝ)+3)
  let errD:=(Fintype.card (U×U):ℝ)*((Fintype.card (Sym2 V⊕(V×Unit)):ℝ)*
      (2*Real.exp (-2*t^2/(C^2*((3:ℝ)^4*(4*b)/Fintype.card V)*(2*3)*((3:ℝ)^2*(4*b))))))
  let errR:=(Fintype.card V+1:ℝ)^4*(Fintype.card U+1:ℝ)^4*
      (2*Real.exp (-2*(ρ*Fintype.card V)^2/((4*(d:ℝ)+3)^2*(2*(2*(4:ℝ)+1)*Fintype.card V))))
  have hprob:1-errD-errR≤μ.probability (ordinarySampledTriangleProfileProperty P F π d · pmin smin j β η a b):=by
    have hh:=ordinary_sampled_triangle_property_common_event P F π d hd hn0 hF hnoshort weight hweight a b ha hb hwlo hwhi L α hL hα hdeg hP he D ε hD hDhi hnear p pmin smin hpmin hp hp1 hsmin hsmin1 q hq hQ s hs hS j hslo hshi t (ρ*Fintype.card V) β η ht (mul_pos hρ hnR) hmargin herr
    convert hh using 1 <;> congr!
  have herrors:errD+errR≤2/(Fintype.card V:ℝ)^2:=by
    have hh:=hN V U (by omega) hu
    convert hh using 1 <;> try ring <;> congr!
  have hgood:1-(errD+errR)≤μ.probability (ordinarySampledTriangleProfileProperty P F π d · pmin smin j β η a b):=by linarith
  have hjoint:=finiteLaw_good_intersection μ E _ (errD+errR) hgood
  have hpos:0<μ.probability (fun σ=>E σ ∧ ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b):=by linarith
  obtain ⟨σ,_,hσ⟩:=finiteLaw_positive_event_exists μ _ hpos
  exact ⟨σ,hσ⟩
end Oberwolfach
