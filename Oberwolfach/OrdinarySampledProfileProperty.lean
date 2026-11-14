module

public import Oberwolfach.OrdinarySampledTwoHubProfileInputs

@[expose] public section
/-! The explicit profile inputs on one fixed sampled graph. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] {r:ℕ}
def ordinarySampledProfileProperty
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (pmin smin:ℝ) (j:Color) (β η a b:ℝ):Prop :=
    let Q:=rawWheelGraph P σ\F
    let H:=rawWheelSpokes π d σ j
    let cmin:=pmin^r*(smin*smin)^(r-1);
    (∀ u u' v w,β*Fintype.card V≤
      (((Finset.univ.filter (fun z=>H z u∧H z u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    ∃ localWeight:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun z=>H z u∧H z u')) r→ℝ,
      (∀ u u' (hne:u≠u') C,a/(Fintype.card V:ℝ)^(r-1)≤localWeight u u' hne C ∧
        localWeight u u' hne C≤(4*b/cmin)/(Fintype.card V:ℝ)^(r-1)) ∧
      (∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun z=>H z u∧H z u'),
        |1-hypergraphWeightedDegree localOrdinaryVertices (localWeight u u' hne) v|≤η)

theorem ordinary_sampled_profile_property_from_inputs
    (P F:SimpleGraph V) (π:Equiv.Perm V) (d:ℕ) (σ:RawWheelOutcome V U Γ Color)
    (p pmin smin:ℝ) (s:U→Color→ℝ) (j:Color) (α t L β η a b D:ℝ)
    (hr:2≤r) (hn:0<(Fintype.card V:ℝ)) (hα:0≤α) (hL:0≤L)
    (hP:∀ v,(1/2+α)*Fintype.card V≤(P.degree v:ℝ)) (hF:∀ v,(F.degree v:ℝ)≤L)
    (hpmin:0<pmin) (hp:pmin≤p) (hp1:p≤1) (hsmin:0<smin) (hsmin1:smin≤1)
    (hslo:∀ u,smin≤s u j) (hshi:∀ u,s u j≤1) (ha:0≤a) (hb:0≤b)
    (hDlo:(Fintype.card V:ℝ)/2≤D) (hDhi:D≤2*Fintype.card V)
    (weight:OrdinaryCycle P r→ℝ)
    (hwlo:∀ C,a/(Fintype.card V:ℝ)^(r-2)≤weight C)
    (hwhi:∀ C,weight C≤b/(Fintype.card V:ℝ)^(r-2))
    (hrows:RawOrdinaryRows P π d 2 Finset.univ p s j t σ)
    (hmargin:β*Fintype.card V≤(pmin^2*smin^2)*(2*α)*Fintype.card V-t-2*L)
    (hdeg:∀ u u',u≠u'→∀ v,ordinaryPairHubSpokes π d σ j u u' v ()→
      |1-ordinaryPairHubLocalDegree P F π d σ j u u' weight D
        (p^r*(s u j*s u' j)^(r-1)) v|≤η):
    ordinarySampledProfileProperty (r:=r) P F π d σ pmin smin j β η a b := by
  exact ordinary_sampled_two_hub_profile_inputs P F π d σ p pmin smin s j α t L β η a b D
    hr hn hα hL hP hF hpmin hp hp1 hsmin hsmin1 hslo hshi ha hb hDlo hDhi weight hwlo hwhi hrows hmargin hdeg
end Oberwolfach
