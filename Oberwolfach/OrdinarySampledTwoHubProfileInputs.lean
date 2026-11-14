module

public import Oberwolfach.OrdinaryDenseTwoHubGeometry
public import Oberwolfach.OrdinaryPairHubCycleWeightBounds
public import Oberwolfach.OrdinaryPairHubDegreeDefinition

@[expose] public section
/-! Explicit weights, degrees and neighbourhoods for all sampled hub pairs. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 16384
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance 100000] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U] {r:ℕ}
theorem ordinary_sampled_two_hub_profile_inputs
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
    let Q:=rawWheelGraph P σ\F
    let H:=rawWheelSpokes π d σ j
    let cmin:=pmin^r*(smin*smin)^(r-1);
    (∀ u u' v w,β*Fintype.card V≤
      (((Finset.univ.filter (fun z=>H z u∧H z u'))∩Q.neighborFinset v∩Q.neighborFinset w).card:ℝ)) ∧
    ∃ localWeight:∀ u u':U,u≠u'→LocalOrdinaryCycle Q F (Finset.univ.filter (fun z=>H z u∧H z u')) r→ℝ,
      (∀ u u' (hne:u≠u') C,a/(Fintype.card V:ℝ)^(r-1)≤localWeight u u' hne C ∧
        localWeight u u' hne C≤(4*b/cmin)/(Fintype.card V:ℝ)^(r-1)) ∧
      (∀ u u' (hne:u≠u'),∀ v∈Finset.univ.filter (fun z=>H z u∧H z u'),
        |1-hypergraphWeightedDegree localOrdinaryVertices (localWeight u u' hne) v|≤η) := by
  intro Q H cmin
  constructor
  · intro u u' v w
    have hg:=ordinary_dense_two_hub_geometry P F π d σ p pmin smin s j α t L hα hL hP hF
      hpmin hp hp1 hsmin hsmin1 hslo hrows u u' v w
    apply hmargin.trans
    convert hg using 1 <;> congr!
  · have hQP:Q≤P:=sdiff_le.trans (retainedGraph_le P (fun e=>σ (Sum.inl e)))
    let localWeight:=fun u u' (_:u≠u') (C:LocalOrdinaryCycle Q F (Finset.univ.filter (fun z=>H z u∧H z u')) r)=>
      weight (localOrdinaryParent hQP C)/(D/2)/(p^r*(s u j*s u' j)^(r-1))
    refine ⟨localWeight,?_,?_⟩
    · intro u u' hne C
      exact ordinary_pair_hub_cycle_weight_bounds P F π d σ j s p pmin smin a b D hr hn hDlo hDhi hpmin hp hp1 hsmin hslo hshi ha hb weight hwlo hwhi u u' C
    · intro u u' hne v hv
      exact hdeg u u' hne v ((Finset.mem_filter.mp hv).2)
end Oberwolfach
