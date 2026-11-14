module

public import Oberwolfach.PrunedOrdinaryClassThreshold
public import Oberwolfach.PrunedActualClassSizeBounds

@[expose] public section
/-! The input data used by the ordinary reference event, for an actual
retained short class and the regular host after pruning. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_ordinary_class_reference_inputs {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (F:W→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:1/2≤δ) (hδA:allowedThreshold Allowed≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D):
    let classify:=fun w=>factorPreparationClass (F w) K
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
    ∀a:Fin k,∀i:Fin K,(e a).val=some i→
    let U:Type:={w:remaining // cf w=(e a).val}
    let Fclass:=fun u:U=>F u.1.1
    let ρ₀:ℝ:=2*min κL κS
    let ρ:=initialIndexDensity U D0;
    3 ≤ i.val+1 ∧ i.val+1 ≤ K ∧ i.val+1∈Allowed ∧
    0<ρ₀ ∧ ρ₀≤ρ ∧ ρ≤1 ∧ ρ*(D0:ℝ)=2*Fintype.card U ∧
    (ρ₀/4)*(n:ℝ)≤Fintype.card U ∧ Fintype.card U≤n ∧
    (∀u:U,(Fclass u).IsRegularOfDegree 2 ∧ AllowedCycleLengths (Fclass u) Allowed ∧
      factorPreparationClass (Fclass u) K=some i) ∧
    ∀(R:SimpleGraph (Fin n)),R.IsRegularOfDegree D0→∀v,
      (cycleThreshold (i.val+1)+α/2)*(n:ℝ)≤(R.degree v:ℝ) :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e a i hi U Fclass ρ₀ ρ
  have ht:=pruned_ordinary_class_threshold hn K hK F hF Allowed hAllowed D hEven hsize hDn
    δ α κL κS hδ hδA hα hL0 hS0 hL hS hdegree a i hi
  have hs:=pruned_actual_class_size_and_density hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree a
  refine ⟨ht.1,ht.2.1,ht.2.2.1,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2.1,hs.2.2.2.2.1,
    hs.2.2.2.2.2,?_,ht.2.2.2.2⟩
  intro u
  refine ⟨hF u.1.1,hAllowed u.1.1,?_⟩
  change classify u.1.1=some i
  exact u.2.trans hi
end Oberwolfach
