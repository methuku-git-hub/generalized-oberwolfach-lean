module

public import Oberwolfach.FactorPrunedProtectedPartition
public import Oberwolfach.FactorClassAssignment
public import Oberwolfach.PreparationWeightsFromAllowedThreshold

@[expose] public section
/-! An actual retained ordinary class has an allowed cycle length and the
pruned regular host remains above that cycle's decomposition threshold. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_ordinary_class_threshold {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
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
    ∀ a:Fin k,∀i:Fin K,(e a).val=some i→
      3 ≤ i.val+1 ∧ i.val+1 ≤ K ∧ i.val+1 ∈ Allowed ∧
      cycleThreshold (i.val+1)≤allowedThreshold Allowed ∧
      ∀R:SimpleGraph (Fin n),R.IsRegularOfDegree D0→∀v,
        (cycleThreshold (i.val+1)+α/2)*(n:ℝ)≤(R.degree v:ℝ) :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e a i hi
  have hmem:(fibres0 (e a).val).Nonempty:=(Finset.mem_filter.mp (e a).property).2
  obtain ⟨w,hw⟩:=hmem
  have hwclass:classify w.val=some i:=by
    have hh:cf w=(e a).val:=(Finset.mem_filter.mp hw).2
    exact hh.trans hi
  have hcls:=((factor_preparation_class hn (F w.val) (hF w.val) Allowed (hAllowed w.val) K hK).2 i hwclass)
  have hbdd:BddAbove (cycleThreshold '' Allowed):=by
    refine ⟨1,?_⟩
    rintro x ⟨r,hr,rfl⟩
    exact cycleThreshold_le_one r
  have hle:cycleThreshold (i.val+1)≤allowedThreshold Allowed:=le_csSup hbdd ⟨_,hcls.2.1,rfl⟩
  have hsmall0:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0.le hS0.le hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by simpa [fibres,cutoff,small,removed,ite_mul] using hsmall0
  have hmarg:(δ+α/2)*(n:ℝ)≤(D0:ℝ):=
    (factor_small_removal_margin D removed.card n δ α (by linarith) hα hdegree hsmall removed.card (le_refl _)).2
  refine ⟨hcls.1,by omega,hcls.2.1,hle,?_⟩
  intro R hR v
  have hn' :=mul_le_mul_of_nonneg_right (show cycleThreshold (i.val+1)+α/2≤δ+α/2 by linarith) (Nat.cast_nonneg n)
  have hh:=hn'.trans hmarg
  simpa only [hR v] using hh
end Oberwolfach
