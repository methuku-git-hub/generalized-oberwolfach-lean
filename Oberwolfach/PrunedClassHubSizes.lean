module

public import Oberwolfach.PrunedClassDensityIdentities
public import Oberwolfach.FactorPrunedProtectedPartition

@[expose] public section
/-! The actual retained classes have the linear hub sizes required by
marked and ordinary sampling, with a floor fixed before the factor family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem factor_pruned_class_hub_sizes {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:1/2≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D):
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
    ∀ a:Fin k,
      let U:Type:={w:remaining // cf w=(e a).val};
      (min κL κS/2)*(n:ℝ)≤Fintype.card U ∧ (Fintype.card U:ℝ)≤n :=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e a U
  have hd:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hi:=factor_pruned_actual_density_identities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hsmall0:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0.le hS0.le hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by
    simpa [fibres,cutoff,small,removed,ite_mul] using hsmall0
  have hmarg:(δ+α/2)*(n:ℝ)≤(D0:ℝ):=
    (factor_small_removal_margin D removed.card n δ α (by linarith) hα hdegree hsmall removed.card (le_refl _)).2
  have hnR:(0:ℝ)≤n:=by positivity
  have hDlo:(n:ℝ)/2≤D0:=by nlinarith
  have hDhi:(D0:ℝ)≤n:=by
    have hh:D0≤n:=by dsimp [D0];omega
    exact_mod_cast hh
  have hDpos:(0:ℝ)≤D0:=by positivity
  have hminpos:(0:ℝ)≤min κL κS:=le_of_lt (lt_min hL0 hS0)
  have hρlo:2*min κL κS ≤ initialIndexDensity U D0:=(hd.2.2.2.2 a).1
  have hρhi:initialIndexDensity U D0≤1:=(hd.2.2.2.2 a).2
  have hmass:initialIndexDensity U D0*(D0:ℝ)=2*Fintype.card U:=by
    have hx:=hi a
    rw [←hx.1]
    exact hx.2
  have hlower:=mul_le_mul_of_nonneg_right hρlo hDpos
  have hupper:=mul_le_mul_of_nonneg_right hρhi hDpos
  have hmul:=mul_le_mul_of_nonneg_left hDlo (show (0:ℝ)≤2*min κL κS by positivity)
  constructor <;> nlinarith
end Oberwolfach
