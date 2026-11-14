module

public import Oberwolfach.PrunedClassDensityIdentities
public import Oberwolfach.FactorPrunedProtectedPartition
public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! The retained long class and the actual regular graph after deleting small
classes supply the input conditions of the long-class reference theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_long_class_reference_inputs {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
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
    ∀ j:Fin k,(e j).val=none→
    let U:Type:={w:remaining // cf w=(e j).val}
    let Fclass:=fun u:U=>F u.1.1
    let ρ₀:ℝ:=2*min κL κS
    let ρ:=initialIndexDensity U D0;
    0<D0 ∧ 0<ρ₀ ∧ ρ₀≤ρ ∧ ρ≤1 ∧ ρ*(D0:ℝ)=2*Fintype.card U ∧
    (∀u:U,(Fclass u).IsRegularOfDegree 2 ∧ AllowedCycleLengths (Fclass u) Allowed ∧
      factorPreparationClass (Fclass u) K=none) ∧
    (n:ℝ)/2≤D0 ∧ (D0:ℝ)≤2*n ∧
    ∀ (R:SimpleGraph (Fin n)),R.IsRegularOfDegree D0→
      (∀v,(allowedThreshold Allowed+α/2)*(n:ℝ)≤(R.degree v:ℝ)) ∧
      ∀ε:ℝ,0≤ε→∀v,|(R.degree v:ℝ)-(D0:ℝ)|≤ε*n :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e j hj U Fclass ρ₀ ρ
  have hdens:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hid:=factor_pruned_actual_density_identities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hsmall0:=factor_small_class_budget K hK classify (n:ℝ) α κL κS (by positivity) hα hL0.le hS0.le hL hS
  have hsmall:(removed.card:ℝ)≤α*n/500:=by simpa [fibres,cutoff,small,removed,ite_mul] using hsmall0
  have hmarg:(δ+α/2)*(n:ℝ)≤(D0:ℝ):=
    (factor_small_removal_margin D removed.card n δ α (by linarith) hα hdegree hsmall removed.card (le_refl _)).2
  have hρ₀:0<ρ₀:=by dsimp [ρ₀];positivity
  have hρlo:ρ₀≤ρ:=(hdens.2.2.2.2 j).1
  have hρhi:ρ≤1:=(hdens.2.2.2.2 j).2
  have hmass:ρ*(D0:ℝ)=2*Fintype.card U:=by
    have heq:ρ=2*((fibres0 (e j).val).card:ℝ)/D0:=(hid j).1.symm
    rw [heq]
    exact (hid j).2
  have hDlo:(n:ℝ)/2≤D0:=by
    have hh:=mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤δ+α/2 by linarith) (Nat.cast_nonneg n)
    nlinarith
  have hDhi:(D0:ℝ)≤2*n:=by
    have hh:D0≤n:=by dsimp [D0];omega
    have hh':(D0:ℝ)≤n:=by exact_mod_cast hh
    nlinarith [show (0:ℝ)≤n by positivity]
  refine ⟨hdens.1,hρ₀,hρlo,hρhi,hmass,?_,hDlo,hDhi,?_⟩
  · intro u
    refine ⟨hF u.1.1,hAllowed u.1.1,?_⟩
    change classify u.1.1=none
    exact u.2.trans hj
  · intro R hR
    constructor
    · intro v
      have hh:=mul_le_mul_of_nonneg_right (show allowedThreshold Allowed+α/2≤δ+α/2 by linarith) (Nat.cast_nonneg n)
      have := hh.trans hmarg
      simpa only [hR v] using this
    · intro ε hε v
      rw [hR v,sub_self,abs_zero]
      positivity
end Oberwolfach
