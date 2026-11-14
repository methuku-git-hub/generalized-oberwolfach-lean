module

public import Oberwolfach.OrdinaryMixedGenericFamily
public import Oberwolfach.MixedSeedResourceSizes
public import Oberwolfach.EmbeddedOrdinaryPairBound

@[expose] public section
/-! Rank and typed pair bounds for the mixed ordinary candidate family. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I:Type} [Fintype V] [Fintype U] [Fintype I] [LinearOrder V] [DecidableEq U]

theorem ordinary_mixed_generic_candidate_bounds
    (π:Equiv.Perm V) (b m r:ℕ) (hm:3≤m) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (f:I→ℕ) (hf:∀i,1≤f i) (hrM:2*(m+1)≤r) (hrO:∀i,2*(f i+2)≤r)
    (wM:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ)
    (wO:∀i,OrderedOrdinaryWheel (U:=U) π b (f i+2)→ℝ)
    (BM:ℝ) (BO:I→ℝ) (hBM:0≤BM) (hBO:∀i,0≤BO i)
    (hwM:∀W,0≤wM W ∧ wM W≤BM/(Fintype.card V:ℝ)^m)
    (hwO:∀i W,0≤wO i W ∧ wO i W≤BO i/(Fintype.card V:ℝ)^(f i+1)):
    let R:=ordinaryMixedGenericResources
      (fun W:MarkedWheel (Prod.fst:V×V→V) Prod.snd Prod.fst Prod.snd m π b
        (fun _ (_:U)=>True) (fun _ (_:U)=>True)=>typedMarkedOccurrenceResources W)
      (fun i (W:OrderedOrdinaryWheel (U:=U) π b (f i+2))=>orderedOrdinaryResources W)
    let w:=ordinaryMixedGenericWeight wM wO
    let C:Option I→ℝ:=fun i=>match i with
      | none=>((m:ℝ)+1)^4*BM
      | some i=>((f i:ℝ)+2)^3*BO i;
    (∀i W,2≤(R i W).card ∧ (R i W).card≤r) ∧
    (∀i W,0≤w i W) ∧ (∀i,0≤C i) ∧
    ∀i e f,resourceOmittedPairWeight (R i) (w i) e f≤C i/(Fintype.card V:ℝ) :=by
  intro R w C
  constructor
  · intro i W
    cases i with
    | none=>
      have hh:=typed_marked_seed_resource_size W
      dsimp [R,ordinaryMixedGenericResources]
      exact ⟨hh.1,hh.2.trans hrM⟩
    | some i=>
      have hh:=ordered_ordinary_seed_resource_size (by have h:=hf i;omega) W
      dsimp [R,ordinaryMixedGenericResources]
      simpa only [Finset.card_map] using And.intro hh.1 (hh.2.trans (hrO i))
  constructor
  · intro i W
    cases i with
    | none=>exact (hwM W).1
    | some i=>exact (hwO i W).1
  constructor
  · intro i
    cases i with
    | none=>dsimp [C];positivity
    | some i=>dsimp [C];have hh:=hBO i;positivity
  · intro i e z
    cases i with
    | none=>
      have hh:=typedMarkedOmittedPair_uniform_bound hm hn hu wM BM hBM hwM e z
      dsimp [R,w,C,ordinaryMixedGenericResources,ordinaryMixedGenericWeight]
      convert hh using 1 <;> congr! 4 <;> simp
    | some i=>
      have hh:=embedded_ordered_ordinary_pair_bound (by have h:=hf i;omega) hn hu (wO i) (BO i) (hBO i) (hwO i) e z
      have hc:(((f i+1:ℕ):ℝ)+1)=(f i:ℝ)+2:=by push_cast;ring
      rw [hc] at hh
      dsimp [R,w,C,ordinaryMixedGenericResources,ordinaryMixedGenericWeight]
      convert hh using 1 <;> congr! 4 <;> simp
end Oberwolfach
