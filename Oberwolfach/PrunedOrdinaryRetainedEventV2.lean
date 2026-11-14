module

public import Oberwolfach.OrdinaryAssignedBoundNamedEvent
public import Oberwolfach.OrdinaryNamedRetainedBudget
public import Oberwolfach.PrunedOrdinaryClassInputs
public import Oberwolfach.OrdinaryAssignedNamedClassEvent
public import Oberwolfach.PrunedOrdinaryClassThreshold
public import Oberwolfach.PrunedActualClassSizeBounds
public import Oberwolfach.OrdinaryAssignedClassAtBound

@[expose] public section
/-! Apply the fixed-length ordinary event to the actual retained class and the
actual regular graph after pruning. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 32768
set_option maxHeartbeats 5000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_ordinary_retained_event_from_bound
    (K d:ℕ) (hK:0<K) (hd:2≤d) (i₀:Fin K) (hi:3 ≤ i₀.val)
    (γ κL κS s₀ βP ηP row ηH L:ℝ)
    (hγ:0<γ) (hL0:0<κL) (hS0:0<κS) (hρ₀:0<2*min κL κS) (hs₀:0<s₀)
    (kH:ℕ) (βH c B:ℝ) (N:ℕ)
    (hbound:ordinaryAssignedClassAtBound i₀.val d K hi hd (cycleThreshold (i₀.val+1)) γ
      (2*min κL κS) s₀ ((2*min κL κS)/4) βP ηP row ηH L
      hρ₀ hs₀ kH βH c B N)
    {W:Type} [Fintype W] {n:ℕ} (hn:N≤n) (hn0:0<n)
    (Factors:W→SimpleGraph (Fin n)) (hFactors:∀w,(Factors w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (Factors w) Allowed)
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ:ℝ) (hδ:1/2≤δ) (hδA:allowedThreshold Allowed≤δ)
    (hL:κL≤(2*γ)/1000) (hS:κS≤(2*γ)/(1000*(K:ℝ)))
    (hdegree:(δ+2*γ)*(n:ℝ)≤D)
    (sOrd θfreq caux:ℝ) (hslo:s₀/2≤sOrd) (hshi:sOrd≤s₀)
    (hsclass:sOrd≤1/(2*(K:ℝ))) (hθfreq:0<θfreq) (hθfreq1:θfreq≤1/100)
    (hcaux:8≤caux) (hda:1/θfreq≤d) (χ:ℝ) (hχ:0≤χ) (a:Bool):
    let classify:=fun w=>factorPreparationClass (Factors w) K
    let fibres:=fun j:Option (Fin K)=>Finset.univ.filter (fun w=>classify w=j)
    let cutoff:=fun j:Option (Fin K)=>if j=none then κL else κS
    let small:=fun j:Option (Fin K)=>((fibres j).card:ℝ)<cutoff j*n
    let removed:=Finset.univ.filter (fun w=>small (classify w))
    let remaining:={w:W // w∉removed}
    let cf:=fun w:remaining=>classify w.val
    let D0:=D-2*removed.card
    let fibres0:=fun j:Option (Fin K)=>Finset.univ.filter (fun w:remaining=>cf w=j)
    let C:=Finset.univ.filter (fun j=>(fibres0 j).Nonempty)
    let k:=C.card
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm;
    ∀ j:Fin k,(e j).val=some i₀→
    let U:Type:={w:remaining // cf w=(e j).val}
    letI : Fintype U := inferInstance
    letI : DecidableEq U := Classical.decEq U
    let Fclass:=fun u:U=>Factors u.1.1
    let hFclass:=fun u:U=>hFactors u.1.1
    let ρ₀:ℝ:=2*min κL κS
    let ρ:=initialIndexDensity U D0;
    ∀ (R:SimpleGraph (Fin n)),R.IsRegularOfDegree D0→
    ∃ weight:OrdinaryCycle R (i₀.val+1)→ℝ,
      (∀ C,c/(n:ℝ)^((i₀.val+1)-2)≤weight C ∧ weight C≤B/(n:ℝ)^((i₀.val+1)-2)) ∧
      (letI : DecidableEq (Fin n) := Classical.decEq (Fin n); ∀ x y,(∑ C,if C.val.val.Adj x y then weight C else 0)=if R.Adj x y then 1 else 0) ∧
    ∀ (Conflict:SimpleGraph (Fin n)) (π:Equiv.Perm (Fin n)),
      (∀v,(Conflict.degree v:ℝ)≤L)→permutationConflictGraph π (3*d)≤Conflict→
      (∀x l,0<l→l<2*d+1→(π^l) x≠x)→
    letI : Nonempty (Fin n) := ⟨⟨0,hn0⟩⟩;
    ordinaryAssignedNamedRetainedClassEvent i₀.val d K hi hd i₀ (cycleThreshold (i₀.val+1)) γ
      ρ₀ s₀ βP ηP row ηH βH c B hρ₀ hs₀ kH R Conflict π Fclass hFclass sOrd θfreq caux ρ χ a weight :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e j hj U Fclass hFclass ρ₀ ρ R hR
  have hin:=pruned_ordinary_class_reference_inputs hn0 K hK Factors hFactors Allowed hAllowed D hEven hsize hDn
    δ (2*γ) κL κS hδ hδA (by positivity) hL0 hS0 hL hS hdegree j i₀ hj
  obtain ⟨_,_,_,hρ₀',hρlo,hρhi,hmass,hUlo,hUhi,hcls,hhost⟩:=hin
  have hgraph:∀v,(cycleThreshold (i₀.val+1)+γ)*(n:ℝ)≤(R.degree v:ℝ):=by
    have hid:(2*γ)/2=γ:=by ring
    intro v
    simpa only [hid] using hhost R hR v
  have hAllowedClass:∀u:U,AllowedCycleLengths (Fclass u) Allowed:=fun u=>(hcls u).2.1
  have hclass:∀u:U,factorPreparationClass (Fclass u) K=some i₀:=fun u=>(hcls u).2.2
  have hnamed:=ordinary_assigned_bound_named_class_event i₀.val d K hi hd (cycleThreshold (i₀.val+1)) γ
      (2*min κL κS) s₀ ((2*min κL κS)/4) βP ηP row ηH L hρ₀ hs₀ kH βH c B N hbound
  obtain ⟨weight,hw,he,hrest⟩:=hnamed n hn hn0 R D0 hR hgraph
  refine ⟨weight, ?_⟩
  constructor
  · exact hw
  constructor
  · exact he
  intro Conflict π hConflict hsub hshort
  have hfirst := @hrest U (inferInstance : Fintype U) (Classical.decEq U) hUlo hUhi i₀ Fclass hFclass Allowed hAllowedClass hclass sOrd θfreq caux hslo hshi hsclass hθfreq hθfreq1 hcaux hda hρlo hρhi Conflict π hConflict hsub hshort
  letI : Nonempty (Fin n):=⟨⟨0,hn0⟩⟩
  have hret := @ordinary_assigned_named_retained_budget n _ U (inferInstance : Fintype U) (Classical.decEq U)
    i₀.val d K hi hd i₀ (cycleThreshold (i₀.val+1)) γ (2*min κL κS) s₀ βP ηP row ηH βH c B
    hρ₀ hs₀ kH R Conflict π Fclass hFclass sOrd θfreq caux (initialIndexDensity U D0) χ a weight hχ hfirst
  dsimp only [ρ, ρ₀]
  exact hret
end Oberwolfach
