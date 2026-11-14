module

public import Oberwolfach.OrdinarySampledTriangleProfileInputs

@[expose] public section
/-! Explicit sampled two-hub weights and four-neighbour inputs for triangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]
def ordinarySampledTriangleProfileProperty
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (pmin smin:ℝ) (j:Color) (β η a b:ℝ):Prop :=
    let Q:=rawWheelGraph P σ\F
    let H:=rawWheelSpokes π d σ j
    let cmin:=pmin^3*(smin*smin)^2;
    (∀ u u' v₁ v₂ v₃ v₄,β*Fintype.card V≤
      ((Finset.univ.filter (fun z=>H z u∧H z u'∧Q.Adj v₁ z∧Q.Adj v₂ z∧Q.Adj v₃ z∧Q.Adj v₄ z)).card:ℝ)) ∧
    ∃ localWeight:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun z=>H z u∧H z u')) 3→ℝ,
      (∀ u u' (hne:u≠u') C,a/(Fintype.card V:ℝ)^2≤localWeight u u' hne C ∧
        localWeight u u' hne C≤(4*b/cmin)/(Fintype.card V:ℝ)^2) ∧
      (∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun z=>H z u∧H z u'),
        |1-hypergraphWeightedDegree localOrdinaryVertices (localWeight u u' hne) v|≤η)

theorem ordinary_sampled_triangle_property_from_inputs
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color) (α t L β η a b D:ℝ)
    (hn:0<(Fintype.card V:ℝ)) (hα:0<α) (hL:0≤L)
    (hP:∀ v,(3/4+α)*Fintype.card V≤(P.degree v:ℝ)) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1) (hsmin:0<smin) (hsmin1:smin≤1)
    (hslo:∀ u,smin≤s u j) (hshi:∀ u,s u j≤1) (ha:0≤a) (hb:0≤b)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (weight:OrdinaryCycle P 3→ℝ)
    (hwlo:∀ C,a/(Fintype.card V:ℝ)≤weight C)
    (hwhi:∀ C,weight C≤b/(Fintype.card V:ℝ))
    (hrows:RawOrdinaryRows P π d 4 Finset.univ p s j t σ)
    (hmargin:β*Fintype.card V≤(pmin^4*smin^4)*(4*(min α (1/4)))*Fintype.card V-t-4*L)
    (hdeg:∀ u u',u≠u'→∀ v,ordinaryPairHubSpokes π d σ j u u' v ()→
      |1-ordinaryPairHubLocalDegree P F π d σ j u u' weight D
        (p^3*(s u j*s u' j)^2) v|≤η):
    ordinarySampledTriangleProfileProperty P F π d σ pmin smin j β η a b := by
  exact ordinary_sampled_triangle_profile_inputs P F π d σ p pmin smin s j α t L β η a b D
    hn hα hL hP hF hpmin hp hp1 hsmin hsmin1 hslo hshi ha hb hDlo hDhi weight hwlo hwhi hrows hmargin hdeg
end Oberwolfach
