module

public import Oberwolfach.OrdinaryMixedPhysicalResourceFiber
public import Oberwolfach.LongMixedSeedCodegrees

@[expose] public section
/-! Physical codegrees for each ordinary-preparation candidate family.
This counts collisions between shifted and unshifted typed arcs by passing
to the same physical edge, with no assumption that the map is injective. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem ordinary_mixed_physical_component_codegrees
    (π:Equiv.Perm (Fin n)) (b m:ℕ) (hm:3≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (ℓ:Fin K→ℕ) (hℓ:∀i,2≤ℓ i)
    (wM:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π b (ℓ i+1)→ℝ)
    (BM:ℝ) (BO:Fin K→ℝ) (hBM:0≤BM) (hBO:∀i,0≤BO i)
    (hwM:∀W,0≤wM W ∧ wM W≤BM/(n:ℝ)^m)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(n:ℝ)^(ℓ i)):
    let R:=longMixedSeedResources
      (fun W:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (ℓ i+1))=>orderedOrdinaryResources W)
    let w:=longMixedSeedWeight wM wO
    let C:Option (Fin K)→ℝ:=fun i=>match i with
      | none=>((m:ℝ)+1)^4*BM
      | some i=>((ℓ i:ℝ)+1)^3*BO i
    ∀i (e f:Sym2 (Fin n)⊕(Fin n×U)),e≠f→
      (∑W,if e∈(R i W).image (ordinaryMixedPhysicalResource π) ∧
        f∈(R i W).image (ordinaryMixedPhysicalResource π) then w i W else 0)≤16*C i/n := by
  intro R w C i e f hef
  have hp:=long_mixed_seed_component_codegrees π b m hm hn hu ℓ hℓ wM wO BM BO hBM hBO hwM hwO
  change ∀i a b,resourceOmittedPairWeight (R i) (w i) a b≤C i/n at hp
  have hw:∀W,0≤w i W:=by
    cases i with
    | none=>exact fun W=>(hwM W).1
    | some i=>exact fun W=>(hwO i W).1
  have hc:0≤C i:=by
    cases i with
    | none=>exact mul_nonneg (pow_nonneg (by positivity) _) hBM
    | some i=>exact mul_nonneg (pow_nonneg (by positivity) _) (hBO i)
  let dA : DecidableEq (((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)) := inferInstance
  letI : DecidableEq (Fin n) := Classical.decEq _
  have hbound:=@physical_resource_pair_weight_bounded_fibers _ _ _ _ (longMixedSeedFamilyFintype i) dA instDecidableEqSum (ordinaryMixedPhysicalResource π) (R i) (w i) hw
    4 (ordinary_mixed_physical_resource_fiber_card π) (C i/n) (div_nonneg hc (by positivity)) (hp i) e f hef
  convert hbound using 1 <;> norm_num <;> ring
end Oberwolfach
