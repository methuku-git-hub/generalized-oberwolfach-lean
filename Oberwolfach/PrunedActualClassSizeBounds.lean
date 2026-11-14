module

public import Oberwolfach.PrunedClassDensityIdentities
public import Oberwolfach.FactorPrunedProtectedPartition

@[expose] public section
/-! Every actual nonempty retained class has linearly many indices, with a
lower fraction fixed from the pruning cutoffs before the family is chosen. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_actual_class_size_and_density {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
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
    ∀a:Fin k,
    let U:Type:={w:remaining // cf w=(e a).val}
    let ρ₀:ℝ:=2*min κL κS
    let ρ:=initialIndexDensity U D0;
    0<ρ₀ ∧ ρ₀≤ρ ∧ ρ≤1 ∧ ρ*(D0:ℝ)=2*Fintype.card U ∧
    (ρ₀/4)*(n:ℝ)≤Fintype.card U ∧ Fintype.card U≤n :=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e a U ρ₀ ρ
  have hdens:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hid:=factor_pruned_actual_density_identities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hsmall0:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0.le hS0.le hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by simpa [fibres,cutoff,small,removed,ite_mul] using hsmall0
  have hmarg:(δ+α/2)*(n:ℝ)≤(D0:ℝ):=
    (factor_small_removal_margin D removed.card n δ α (by linarith) hα hdegree hsmall removed.card (le_refl _)).2
  have hρ₀:0<ρ₀:=by dsimp [ρ₀];positivity
  have hρlo:ρ₀≤ρ:=(hdens.2.2.2.2 a).1
  have hρhi:ρ≤1:=(hdens.2.2.2.2 a).2
  have hmass:ρ*(D0:ℝ)=2*Fintype.card U:=by
    have heq:ρ=2*((fibres0 (e a).val).card:ℝ)/D0:=(hid a).1.symm
    rw [heq]
    exact (hid a).2
  have hD0:(0:ℝ)<D0:=by exact_mod_cast hdens.1
  have hDlo:(n:ℝ)/2≤D0:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤δ+α/2 by linarith) (Nat.cast_nonneg n)
    nlinarith
  have hDhi:(D0:ℝ)≤n:=by
    have hh:D0≤n:=by dsimp [D0];omega
    exact_mod_cast hh
  have hmul:=mul_le_mul_of_nonneg_right hρlo hD0.le
  have hmul2:=mul_le_mul_of_nonneg_left hDlo hρ₀.le
  have hmul3:=mul_le_mul_of_nonneg_right hρhi hD0.le
  refine ⟨hρ₀,hρlo,hρhi,hmass,?_,?_⟩
  · nlinarith
  · have hh:(Fintype.card U:ℝ)≤n:=by nlinarith [Nat.cast_nonneg (α:=ℝ) n]
    exact_mod_cast hh
end Oberwolfach
