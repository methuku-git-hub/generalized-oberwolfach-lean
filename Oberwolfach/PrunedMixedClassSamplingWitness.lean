module

public import Oberwolfach.MixedAssignedSamplingWitness
public import Oberwolfach.PrunedClassDensityIdentities

@[expose] public section
/-! All nonempty retained classes supply the original marked and ordinary
sampling recipes, with one probability vector for the shared exposure. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem pruned_mixed_classes_sampling_witness {W:Type} [Fintype W] {n:ℕ} (hn:0<n)
    (K:ℕ) (hK:0<K) (F:W→SimpleGraph (Fin n)) (hF:∀w,(F w).IsRegularOfDegree 2)
    (Allowed:Set ℕ) (hAllowed:∀w,AllowedCycleLengths (F w) Allowed)
    (D:ℕ) (hEven:Even D) (hsize:Fintype.card W=D/2) (hDn:D≤n)
    (δ α κL κS:ℝ) (hδ:0≤δ) (hα:0<α)
    (hL0:0<κL) (hS0:0<κS) (hL:κL≤α/1000) (hS:κS≤α/(1000*(K:ℝ)))
    (hdegree:(δ+α)*(n:ℝ)≤D)
    (m d:ℕ) (hm:7≤m) (hd:2≤d) (s θ:ℝ) (hs0:0≤s) (hs1:s≤1/100)
    (hsclass:s≤1/(2*(K:ℝ))) (hθ:0<θ) (hθ1:θ≤1/100)
    (hda:1/θ≤d) (hcut:(1/((m:ℝ)+1))/(d:ℝ)≤θ):
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
    let U:=fun j:Fin k=>{w:remaining // cf w=(e j).val}
    let Fclass:=fun j (u:U j)=>F u.1.1
    let hFclass:=fun j (u:U j)=>hF u.1.1
    let label:=fun j:Fin k=>(e j).val
    let ρ₀:ℝ:=2*min κL κS
    let ρ:=fun j:Fin k=>initialIndexDensity (U j) D0
    let q:=mixedAssignedIntervalProbability K m θ label Fclass hFclass
    let sco:=mixedAssignedSpokeProbability K m s θ label Fclass hFclass;
    ∃ (p kmark p₂ k₂ udens:Fin k→ℝ),
      (∀i,0≤p i ∧ 0≤kmark i ∧ 0≤p₂ i ∧ 0≤k₂ i ∧ 0≤udens i ∧
        2*p i+2*kmark i+2*p₂ i+2*k₂ i+udens i=ρ i) ∧
      (∀i w j,0≤q i w j) ∧ (∀i w,∑j,q i w j≤1/8) ∧
      (∀i w j,0≤sco i w j) ∧ (∀i w,∑j,sco i w j≤ intervalUncoveredProbability d (∑j,q i w j)) ∧
      (∀i,label i=none→2*p i=ρ i*(1/100:ℝ) ∧ 2*kmark i=ρ i*((1/100:ℝ)/(m:ℝ)) ∧
        ρ₀/8≤p₂ i ∧ ρ₀/(6*((m:ℝ)+1))≤k₂ i ∧
        p₂ i*(D0:ℝ)=∑w,longAssignedApproxOrdinaryWeight (Fclass i) (hFclass i) K m θ w ∧
        k₂ i*(D0:ℝ)=∑w,longAssignedApproxMarkedWeight (Fclass i) (hFclass i) K m θ w ∧
        udens i*(D0:ℝ)=2*∑w,(1-(1/100:ℝ)-(1/100:ℝ)/(m:ℝ)-longAssignedApproxMarkedWeight (Fclass i) (hFclass i) K m θ w-longAssignedApproxOrdinaryWeight (Fclass i) (hFclass i) K m θ w) ∧
        ρ₀*((1/100:ℝ)/(m:ℝ))/2≤kmark i ∧
        ∀w,q i w false=(1/100:ℝ)/(m:ℝ) ∧ sco i w false=1/100) ∧
      (∀i j,label i=some j→kmark i=0 ∧ k₂ i=0 ∧ 2*p i=ρ i*s ∧ ρ i/4≤p₂ i ∧
        p₂ i*(D0:ℝ)=∑w,(ordinaryAssignedLongWeight (Fclass i) (hFclass i) K θ ((m:ℝ)+1) w+ordinaryAssignedShortWeight (Fclass i) (hFclass i) K j s θ ((m:ℝ)+1) w) ∧
        udens i*(D0:ℝ)=2*∑w,(1-s-ordinaryAssignedLongWeight (Fclass i) (hFclass i) K θ ((m:ℝ)+1) w-ordinaryAssignedShortWeight (Fclass i) (hFclass i) K j s θ ((m:ℝ)+1) w) ∧
        ∀w,q i w false=0 ∧ sco i w false=s) :=by
  intro classify fibres cutoff small removed remaining cf D0 fibres0 C k e U Fclass hFclass label ρ₀ ρ q sco
  have hdens:=factor_pruned_initial_index_densities hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  have hid:=factor_pruned_actual_density_identities hn K hK classify D hEven hsize hDn δ α κL κS
    hδ hα hL0 hS0 hL hS hdegree
  have hρ₀:0<ρ₀:=by dsimp [ρ₀];positivity
  have hρlo:∀i,ρ₀≤ρ i:=fun i=>(hdens.2.2.2.2 i).1
  have hρhi:∀i,ρ i≤1:=fun i=>(hdens.2.2.2.2 i).2
  have hD:0<(D0:ℝ):=by exact_mod_cast hdens.1
  have hmass:∀i,ρ i*(D0:ℝ)=2*Fintype.card (U i):=by
    intro i
    have heq:ρ i=2*((fibres0 (e i).val).card:ℝ)/D0:=(hid i).1.symm
    rw [heq]
    exact (hid i).2
  have hallow:∀i (u:U i),AllowedCycleLengths (Fclass i u) Allowed:=fun _ u=>hAllowed u.1.1
  have hclass:∀i (u:U i),factorPreparationClass (Fclass i u) K=label i:=fun _ u=>u.2
  exact mixed_assigned_classes_sampling_witness hn K m d hK hm hd label Fclass hFclass Allowed hallow hclass s θ ρ₀ D0 ρ
    hs0 hs1 hsclass hθ hθ1 hda hcut hρ₀ hρlo hρhi hD hmass
end Oberwolfach
