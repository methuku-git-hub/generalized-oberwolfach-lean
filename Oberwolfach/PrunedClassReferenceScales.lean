module

public import Oberwolfach.PrunedInitialIndexDensities
public import Oberwolfach.LongReferenceFixedScales

@[expose] public section
/-! Apply the density-uniform seed scales to the actual retained classes. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
theorem factor_pruned_reference_seed_lower_bounds {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (m:ℕ) (hm:1≤m) (K:ℕ) (hK:0<K) (classify:W→Option (Fin K))
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
    let ρ₀:=2*min κL κS
    let sstar:ℝ:=1/100
    let tstar:ℝ:=sstar/(m:ℝ)
    let kstar:ℝ:=ρ₀*tstar/4;
    0<ρ₀ ∧ 0<tstar ∧ 0<kstar ∧ ∀ a:Fin k,
      let U:Type:={w:remaining // cf w=(e a).val}
      let ρ:=initialIndexDensity U D0
      let p:=ρ*sstar/2
      let kref:=p/(m:ℝ);
      ρ₀≤ρ ∧ ρ≤1 ∧ kstar≤p ∧ kstar≤kref :=by
  intro fibres cutoff small removed remaining cf D0 fibres0 C k e ρ₀ sstar tstar kstar
  have hρ0:0<ρ₀:=by dsimp [ρ₀]; positivity
  have hh:=long_reference_fixed_scales m hm ρ₀ hρ0
  have hd:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  refine ⟨hρ0,hh.2.2.1,hh.2.2.2.2.2.1,?_⟩
  intro a U ρ p kref
  have hda:=hd.2.2.2.2 a
  exact ⟨hda.1,hda.2,(hh.2.2.2.2.2.2.2.2.2 ρ hda.1).1,
    (hh.2.2.2.2.2.2.2.2.2 ρ hda.1).2⟩
end Oberwolfach
