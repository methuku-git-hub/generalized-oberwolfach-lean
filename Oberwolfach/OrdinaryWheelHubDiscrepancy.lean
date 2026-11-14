module

public import Oberwolfach.MarkedMixedHubDiscrepancy
public import Oberwolfach.OrderedOrdinaryWheelResources

@[expose] public section
/-! Exact hub contribution of a variable-length ordinary wheel when its
spokes are in the unmarked part of the common ambient resource set. -/
set_option autoImplicit false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]

def ordinaryWheelSpokePairs {π:Equiv.Perm V} {b r:ℕ}
    (W:OrderedOrdinaryWheel (U:=U) π b r):Finset (V×U) :=
  Finset.univ.image (fun i:Fin r=>(W.1.val i,W.2))

theorem ordinary_wheel_spoke_pairs_card {π:Equiv.Perm V} {b r:ℕ}
    (W:OrderedOrdinaryWheel (U:=U) π b r):
    (ordinaryWheelSpokePairs W).card=r := by
  unfold ordinaryWheelSpokePairs
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j h
    apply permutationSeparated_injective π b W.1.val W.1.property
    exact congrArg Prod.fst h

theorem ordinary_wheel_unmarked_hub_discrepancy {π:Equiv.Perm V} {b r:ℕ}
    (HK:V→U→Prop) (m:ℕ) (W:OrderedOrdinaryWheel (U:=U) π b r)
    (hHK:∀i,¬HK (W.1.val i) W.2) (u:U):
    markedFiniteHubDiscrepancy HK m (ordinaryWheelSpokePairs W) u =
      if u=W.2 then (r:ℤ) else 0 := by
  have hmark:(ordinaryWheelSpokePairs W).filter (fun s=>s.2=u∧HK s.1 s.2)=∅ := by
    ext s
    simp only [Finset.mem_filter]
    constructor
    · intro hs
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hs.1
      exact False.elim (hHK i (by simpa only [←hi] using hs.2.2))
    · intro hs
      simp at hs
  by_cases hu:u=W.2
  · have hunmark:(ordinaryWheelSpokePairs W).filter (fun s=>s.2=u∧¬HK s.1 s.2)=ordinaryWheelSpokePairs W := by
      ext s
      constructor
      · exact fun hs=>(Finset.mem_filter.mp hs).1
      · intro hs
        obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hs
        apply Finset.mem_filter.mpr
        refine ⟨hs,?_,?_⟩
        · simpa only [←hi] using hu.symm
        · simpa only [←hi] using hHK i
    rw [if_pos hu]
    unfold markedFiniteHubDiscrepancy
    rw [hmark,hunmark,ordinary_wheel_spoke_pairs_card]
    simp
  · have hempty:(ordinaryWheelSpokePairs W).filter (fun s=>s.2=u∧¬HK s.1 s.2)=∅ := by
      ext s
      simp only [Finset.mem_filter]
      constructor
      · intro hs
        obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hs.1
        apply False.elim
        apply hu
        simpa only [←hi] using hs.2.1.symm
      · intro hs
        simp at hs
    simp [markedFiniteHubDiscrepancy,hmark,hempty,hu]
end Oberwolfach
