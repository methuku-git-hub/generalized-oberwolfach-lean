module

public import Oberwolfach.FactorPrunedClassIndices

@[expose] public section
/-! Retained long and ordinary classes have their own density lower bounds;
the ordinary cutoff may be selected after the long cutoff. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_class_specific_density {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0≤κL) (hS0:0≤κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
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
    (∀a,(e a).val=none→2*κL≤ρ a) ∧
    (∀a i,(e a).val=some i→2*κS≤ρ a) :=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ
  have hp:=factor_pruned_family_parameters hn K hK classify D hEven hsize hDn δ α κL κS hδ hα hL0 hS0 hL hS hdegree
  have hlow:∀a,2*cutoff (e a).val≤ρ a:=by
    intro a
    have hm:(fibres0 (e a).val).Nonempty:=(Finset.mem_filter.mp (e a).property).2
    obtain ⟨w,hw⟩:=hm
    have hw':cf w=(e a).val:=(Finset.mem_filter.mp hw).2
    exact hp.2.2.2.2 (e a).val ⟨w,hw'⟩
  constructor
  · intro a ha
    have hh:=hlow a
    simpa [cutoff,ha] using hh
  · intro a i ha
    have hh:=hlow a
    simpa [cutoff,ha] using hh
end Oberwolfach
