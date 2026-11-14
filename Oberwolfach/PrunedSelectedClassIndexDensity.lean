module

public import Oberwolfach.Vortex
public import Oberwolfach.PrunedSelectedClassHostParameters
public import Oberwolfach.LongBinaryPartitionParameters

@[expose] public section
/-! The original pruning construction supplies the even host degree and
exact density data for each actual, nonempty selected class subtype. -/
set_option autoImplicit false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_selected_class_index_density_data {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS ρ₀:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D) (hρ₀:ρ₀≤2*min κL κS):
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
    ∀a:Fin k, initialIndexDensity ↥(fibres0 (e a).val) D0=ρ a ∧
      ρ₀ ≤ initialIndexDensity ↥(fibres0 (e a).val) D0:=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e m ρ
  have h:=pruned_selected_class_host_parameters hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  dsimp only at h
  intro a
  have heq:initialIndexDensity ↥(fibres0 (e a).val) D0=ρ a:=by
    simp only [initialIndexDensity, ρ, m, Fintype.card_coe]
  exact ⟨heq,heq.symm ▸ (hρ₀.trans (h.2.2.2.2.1 a))⟩

end Oberwolfach
