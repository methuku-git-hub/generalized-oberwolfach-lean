module

public import Oberwolfach.FactorPrunedClassIndices
public import Oberwolfach.Vortex

@[expose] public section
/-! The retained long class has its own density lower bound, independent of
the later short-class cutoff; the common partition still has a positive
lower bound for every retained class. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_long_class_independent_density
    {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS ρ₀:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D) (hρ₀:ρ₀≤2*κL):
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
    0<D0 ∧ Even D0 ∧ 0<k ∧ k≤K+1 ∧
    (∀a,0≤ρ a) ∧ (∑a,ρ a)=1 ∧ (∀a,2*min κL κS≤ρ a) ∧
    (∀a,ρ a/2*D0=Fintype.card ↥(fibres0 (e a).val)) ∧
    ∀a:Fin k,(e a).val=none→
      initialIndexDensity ↥(fibres0 (e a).val) D0=ρ a ∧ ρ₀≤ initialIndexDensity ↥(fibres0 (e a).val) D0 :=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ
  have hi:=factor_pruned_class_indices hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  have hp:=factor_pruned_family_parameters hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0.le hS0.le hL hS hdegree
  dsimp only at hi hp
  obtain ⟨hD0,hEven0,hk,hkBound,hmPos,hmSum,hρPos,hρSum,hρsize,hρmin⟩:=hi
  refine ⟨hD0,hEven0,hk,hkBound,fun a=>(hρPos a).le,hρSum,hρmin,?_,?_⟩
  · intro a
    simpa only [Fintype.card_coe] using hρsize a
  · intro a hnone
    have ha:(fibres0 (e a).val).Nonempty:=(Finset.mem_filter.mp (e a).property).2
    obtain ⟨w,hw⟩:=ha
    have hw':cf w=(e a).val:=(Finset.mem_filter.mp hw).2
    have hLong:=hp.2.2.2.2 (e a).val ⟨w,hw'⟩
    have hcut:cutoff (e a).val=κL:=by dsimp [cutoff];rw [hnone];simp
    have hρLong:2*κL≤ρ a:=by simpa only [ρ,m,fibres0,cf,D0,removed,small,fibres,cutoff,hnone,if_true] using hLong
    have heq:initialIndexDensity ↥(fibres0 (e a).val) D0=ρ a:=by
      simp only [initialIndexDensity,ρ,m,Fintype.card_coe]
    exact ⟨heq,heq.symm ▸ hρ₀.trans hρLong⟩
end Oberwolfach
