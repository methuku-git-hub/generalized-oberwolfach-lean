module

public import Oberwolfach.PrunedLongClassIndependentDensity
public import Oberwolfach.FactorClassAssignment

@[expose] public section
/-! The retained long fibre has the exact class and density inputs required
by the selector, with the early long density independent of the short cutoff. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_long_selector_inputs
    {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (F:W→SimpleGraph (Fin n))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS ρ₀:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D) (hρ₀:ρ₀≤2*κL):
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
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm
    let ρ:=fun a:Fin k=>2*((fibres0 (e a).val).card:ℝ)/(D0:ℝ);
    0<D0 ∧ Even D0 ∧ 0<k ∧ k≤K+1 ∧
    (∀a,0≤ρ a) ∧ (∑a,ρ a)=1 ∧ (∀a,2*min κL κS≤ρ a) ∧
    ∀a:Fin k,(e a).val=none→
      initialIndexDensity ↥(fibres0 (e a).val) D0=ρ a ∧ ρ₀ ≤ initialIndexDensity ↥(fibres0 (e a).val) D0 ∧
      (∀u:↥(fibres0 (e a).val),factorPreparationClass (F u.val.val) K=none) :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e ρ
  have h:=pruned_long_class_independent_density hn K hK classify D hEven hsize hDn δ α κL κS ρ₀ hδ hα hL0 hS0 hL hS hdegree hρ₀
  obtain ⟨hD,hEven0,hk,hkbound,hρpos,hρsum,hρmin,_,hlong⟩:=h
  refine ⟨hD,hEven0,hk,hkbound,hρpos,hρsum,hρmin,?_⟩
  intro a hnone
  obtain ⟨heq,hlo⟩:=hlong a hnone
  refine ⟨heq,hlo,?_⟩
  intro u
  have hu:cf u.val=(e a).val:=(Finset.mem_filter.mp u.property).2
  simpa only [cf,classify,hnone] using hu
end Oberwolfach
