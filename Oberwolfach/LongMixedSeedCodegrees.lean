module

public import Oberwolfach.LongAssignedMixedSeedFamilies
public import Oberwolfach.EmbeddedOrdinaryPairBound
public import Oberwolfach.TypedMarkedLoadBounds

@[expose] public section
/-! The original marked and ordinary wheel seed bounds imply the pair
bounds needed for the common sampled resource matching. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n K:ℕ} {U:Type} [Fintype U] [DecidableEq U]

theorem long_mixed_seed_component_codegrees
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
    ∀i (e f:((Fin n×Fin n)⊕(Fin n×Fin n))⊕(Bool×Fin n×U)),
      resourceOmittedPairWeight (R i) (w i) e f≤C i/n := by
  intro R w C i e f
  cases i with
  | none=>
    have hn':0<Fintype.card (Fin n):=by simpa using hn
    have hu':Fintype.card U≤Fintype.card (Fin n):=by simpa using hu
    have h:=typedMarkedOmittedPair_uniform_bound hm hn' hu' wM BM hBM (by simpa using hwM) e f
    dsimp [R,w,C,longMixedSeedResources,longMixedSeedWeight]
    convert h using 1 <;> congr! 4 <;> simp
  | some i=>
    have hn':0<Fintype.card (Fin n):=by simpa using hn
    have hu':Fintype.card U≤Fintype.card (Fin n):=by simpa using hu
    have h:=embedded_ordered_ordinary_pair_bound (hℓ i) hn' hu' (wO i) (BO i) (hBO i) (by simpa using hwO i) e f
    dsimp [R,w,C,longMixedSeedResources,longMixedSeedWeight]
    convert h using 1 <;> congr! 4 <;> simp
end Oberwolfach
