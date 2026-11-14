module

public import Oberwolfach.FactorPrunedFamilyParameters
public import Oberwolfach.FactorClassIndexBound

@[expose] public section
/-! The actual retained classes, reindexed by Fin k, satisfy all numerical
hypotheses of the protected regular partition simultaneously. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_class_indices {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
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
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
    let m:=fun a:Fin k=>(fibres0 (e a).val).card
    let ρ:=fun a:Fin k=>2*(m a:ℝ)/(D0:ℝ);
    0<D0 ∧ Even D0 ∧ 0<k ∧ k≤K+1 ∧ (∀ a,0<m a) ∧
    (∑ a,m a)=D0/2 ∧ (∀ a,0<ρ a) ∧ (∑ a,ρ a)=1 ∧
    (∀ a,ρ a/2*D0=m a) ∧ (∀ a,2*min κL κS≤ρ a):=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ
  have hp:=factor_pruned_family_parameters hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0.le hS0.le hL hS hdegree
  have hp':0<D0 ∧ Fintype.card remaining=D0/2 ∧ Even D0 ∧
      (∀ j,(∃ w:remaining,cf w=j)→2*cutoff j≤
        2*((Finset.univ.filter (fun w:remaining=>cf w=j)).card:ℝ)/D0):=by
    exact ⟨hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.2⟩
  have hsz:2*Fintype.card remaining=D0:=by
    rw [hp'.2.1]
    obtain ⟨t,ht⟩:=hp'.2.2.1
    omega
  have hc:=factor_nonempty_class_indices cf D0 hp'.1 hsz
  have hbound:k≤K+1:=factor_nonempty_class_count_bound K cf
  have hlow:∀ a,2*min κL κS≤ρ a:=by
    intro a
    have ha:(fibres0 (e a).val).Nonempty:=(Finset.mem_filter.mp (e a).property).2
    obtain ⟨w,hw⟩:=ha
    have hw':cf w=(e a).val:=(Finset.mem_filter.mp hw).2
    have hρ:=hp'.2.2.2 (e a).val ⟨w,hw'⟩
    have hmin:min κL κS≤cutoff (e a).val:=by
      dsimp [cutoff]
      split
      · exact min_le_left _ _
      · exact min_le_right _ _
    have hh:=mul_le_mul_of_nonneg_left hmin (by norm_num: (0:ℝ)≤2)
    exact hh.trans hρ
  exact ⟨hp'.1,hp'.2.2.1,hc.1,hbound,hc.2.1,hc.2.2.1,hc.2.2.2.1,
    hc.2.2.2.2.1,hc.2.2.2.2.2,hlow⟩
end Oberwolfach
