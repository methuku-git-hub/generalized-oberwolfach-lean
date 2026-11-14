module

public import Oberwolfach.PrunedClassHubSizes

@[expose] public section
/-! Uniform density and hub-size parameters for every actual nonempty class,
chosen before the order and the prescribed factors. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem factor_pruned_uniform_sampling_inputs (K:ℕ) (hK:0<K) (α κL κS:ℝ)
    (hα:0<α) (hα1:α≤1) (hL0:0<κL) (hS0:0<κS)
    (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ))):
    let ρ₀:=2*min κL κS
    let ω:=min κL κS/2;
    0<ρ₀ ∧ ρ₀≤1 ∧ 0<ω ∧
    ∀ {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
      (classify:W→Option (Fin K)) (D:ℕ) (hEven:Even D)
      (hsize:Fintype.card W=D/2) (hDn:D≤n) (δ:ℝ) (hδ:1/2≤δ)
      (hdegree:(δ+α)*(n:ℝ)≤D),
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
    0<D0 ∧ Even D0 ∧ 0<k ∧ k≤K+1 ∧ ∀ a:Fin k,
      let U:Type:={w:remaining // cf w=(e a).val};
      ρ₀ ≤ initialIndexDensity U D0 ∧ initialIndexDensity U D0≤1 ∧
      ω*(n:ℝ)≤Fintype.card U ∧ (Fintype.card U:ℝ)≤n := by
  intro ρ₀ ω
  have hmin:0<min κL κS:=lt_min hL0 hS0
  have hρ0:0<ρ₀:=by dsimp [ρ₀];positivity
  have hρ1:ρ₀≤1:=by dsimp [ρ₀];have hh:=min_le_left κL κS;linarith
  have hω:0<ω:=by dsimp [ω];positivity
  refine ⟨hρ0,hρ1,hω,?_⟩
  intro W _ n hn classify D hEven hsize hDn δ hδ hdegree
    fibres cutoff small removed remaining cf D0 fibres0 C k e
  have hd:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    (by linarith) hα hL0 hS0 hL hS hdegree
  have hs:=factor_pruned_class_hub_sizes hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  refine ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,?_⟩
  intro a U
  exact ⟨(hd.2.2.2.2 a).1,(hd.2.2.2.2 a).2,(hs a).1,(hs a).2⟩
end Oberwolfach
