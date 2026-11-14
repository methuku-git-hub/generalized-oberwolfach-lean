module

public import Oberwolfach.PrunedInitialIndexDensities

@[expose] public section
/-! The mass identity required by the actual class preparation, for exactly
those factor indices retained by the class-pruning procedure. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem factor_pruned_actual_density_identities {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
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
    ∀ a:Fin k,
      let U:Type:={w:remaining // cf w=(e a).val};
      let ρ:ℝ:=2*((fibres0 (e a).val).card:ℝ)/(D0:ℝ);
      ρ=initialIndexDensity U D0 ∧ ρ*(D0:ℝ)=2*Fintype.card U :=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e a U ρ
  have hh:=factor_pruned_class_indices hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  obtain ⟨hD0,hEven0,hk,hkbound,hmpos,hmsum,hρpos,hρsum,hmarg,hρlow⟩:=hh
  have hcard:Fintype.card U=(fibres0 (e a).val).card:=by
    simp only [U,fibres0,Fintype.card_subtype,Finset.filter_mem_eq_inter,Finset.univ_inter]
  refine ⟨?_,?_⟩
  · dsimp only [initialIndexDensity,ρ];rw [hcard]
  · have hD0R:(D0:ℝ)≠0:=by exact_mod_cast (ne_of_gt hD0)
    dsimp only [ρ];rw [hcard];field_simp
end Oberwolfach
