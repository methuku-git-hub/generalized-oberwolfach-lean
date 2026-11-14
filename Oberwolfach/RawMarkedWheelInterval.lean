module

public import Oberwolfach.LongMixedRawHubPreservation

@[expose] public section
/-! The marked vertex of a sampled wheel belongs to one uniquely determined
raw interval of the wheel's hub. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color] {tail head:E→V} {ktail khead:K→V}

theorem raw_marked_wheel_unique_interval
    (π:Equiv.Perm V) (d m b:ℕ) (σ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (W:MarkedWheel tail head ktail khead m π b (rawMarkedPairSpokes π d σ g j false)
      (rawMarkedPairSpokes π d σ g j true)):
    ∃! a,rawIntervalColouredStart π d (fun x=>σ (Sum.inr (W.2.val,x))) a g ∧
      W.1.val 0∈permutationWindow π 0 (d-1) a :=by
  have h:rawIntervalCovered π d (fun x=>σ (Sum.inr (W.2.val,x))) (W.1.val 0) g:=by
    apply (rawIntervalState_interval_iff π d _ _ g).mp
    simpa only [rawMarkedPairSpokes,rawMarkedSpokes,rawIntervalFamilyState] using W.2.property.1
  obtain ⟨a,ha,hxa⟩:=h
  refine ⟨a,⟨ha,hxa⟩,?_⟩
  intro b hb
  have hxa':W.1.val 0∈permutationWindow π 0 d a:=
    permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) a hxa
  have hxb':W.1.val 0∈permutationWindow π 0 d b:=
    permutationWindow_mono π (le_refl 0) (Nat.sub_le _ _) b hb.2
  exact (rawInterval_coloured_start_unique π d _ _ b a g g hb.1 ha hxb' hxa').1
end Oberwolfach

namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color E K:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  [Fintype Γ] [Fintype Color] {tail head:E→V} {ktail khead:K→V}

theorem raw_marked_wheel_interval_unique_position
    (π:Equiv.Perm V) (d m b:ℕ) (hd:1≤d)
    (hnoshort:∀x k,0<k→k<d→(π^k) x≠x)
    (σ:RawMarkedOutcome V U Γ Color) (g:Γ) (j:Color)
    (W:MarkedWheel tail head ktail khead m π b (rawMarkedPairSpokes π d σ g j false)
      (rawMarkedPairSpokes π d σ g j true)):
    ∃ a,rawIntervalColouredStart π d (fun x=>σ (Sum.inr (W.2.val,x))) a g ∧
      ∃! i:Fin d,(π^i.val) a=W.1.val 0 :=by
  obtain ⟨a,⟨ha,hw⟩,huniq⟩:=raw_marked_wheel_unique_interval π d m b σ g j W
  obtain ⟨i,hi⟩:=(permutationWindow_mem_iff π 0 (d-1) a (W.1.val 0)).mp hw
  have hi_d:i.val<d:=by omega
  let q:Fin d:=⟨i.val,hi_d⟩
  refine ⟨a,ha,q,?_,?_⟩
  · simpa only [pow_zero,Equiv.Perm.one_apply] using hi
  · intro k hk
    have hinj:=permutation_short_interval_injective π d hnoshort a
    apply hinj
    exact hk.trans (by simpa only [pow_zero,Equiv.Perm.one_apply] using hi.symm)
end Oberwolfach
