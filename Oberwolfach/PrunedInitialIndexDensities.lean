module

public import Oberwolfach.FactorPrunedClassIndices
public import Oberwolfach.Vortex

@[expose] public section
/-! Each actual retained class supplies the fixed positive lower density
required before the marked-vortex and seed parameters are chosen. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_initial_index_densities {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
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
    let e:Fin k≃↥C:=(Fintype.equivFinOfCardEq (Fintype.card_coe C)).symm;
    0<D0 ∧ Even D0 ∧ 0<k ∧ k≤K+1 ∧
    (∀ a:Fin k,
      let U:Type:={w:remaining // cf w=(e a).val};
      2*min κL κS ≤ initialIndexDensity U D0 ∧ initialIndexDensity U D0 ≤ 1):=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e
  have hh:=factor_pruned_class_indices hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  dsimp only at hh
  obtain ⟨hD0,hEven0,hk,hkbound,hmpos,hmsum,hρpos,hρsum,hmarg,hρlow⟩:=hh
  refine ⟨hD0,hEven0,hk,hkbound,?_⟩
  intro a U
  have hcard:Fintype.card U=(fibres0 (e a).val).card:=by
    simp only [U,fibres0,Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hρeq:initialIndexDensity U D0=2*((fibres0 (e a).val).card:ℝ)/D0:=by
    dsimp only [initialIndexDensity];rw [hcard]
  rw [hρeq]
  refine ⟨hρlow a,?_⟩
  have hsingle:2*((fibres0 (e a).val).card:ℝ)/D0≤
      ∑ b:Fin k,2*((fibres0 (e b).val).card:ℝ)/D0:=by
    apply Finset.single_le_sum (fun b _=>le_of_lt (hρpos b)) (Finset.mem_univ a)
  exact hsingle.trans_eq hρsum
end Oberwolfach
