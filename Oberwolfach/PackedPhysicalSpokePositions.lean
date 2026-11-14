module

public import Oberwolfach.ActualSelectedPackingPositions

@[expose] public section
/-! The manuscript's selected positions, defined using physical covered spokes,
coincide with the positions whose marked wheel has that interval root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def packedPhysicalSpokePositions
    {V U E L:Type} [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:L→V) (m b d:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U) (a:V):Finset ℕ:=
  (Finset.range d).filter (fun j=>∃W∈M,Sum.inr ((π^j) a,hub)∈markedWheelPhysicalResources W)

theorem packed_physical_spoke_positions_eq_marked_roots
    {V U E L:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:L→V) (m b d:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U) (a:V)
    (Ord:Finset V)
    (hOrd:∀W∈M,W.2.val=hub→∀i:Fin (m+1),i.val≠0→W.1.val i∈Ord)
    (havoid:Disjoint (permutationWindow π 0 d a) Ord):
    packedPhysicalSpokePositions tail head ktail khead m b d π H₀ Hₖ M hub a=
      packedMarkedPositions tail head ktail khead m b d π H₀ Hₖ M hub a:=by
  classical
  ext j
  simp only [packedPhysicalSpokePositions,packedMarkedPositions,Finset.mem_filter]
  constructor
  · rintro ⟨hj,W,hW,hw⟩
    have hsp:W.2.val=hub ∧ (π^j) a∈Finset.univ.image W.1.val:=
      (markedWheelPhysicalResources_spoke W ((π^j) a) hub).mp hw
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hsp.2
    have hzero:i.val=0:=by
      by_contra hn
      have ho:(π^j) a∈Ord:=by rw [←hi];exact hOrd W hW hsp.1 i hn
      have hw':(π^j) a∈permutationWindow π 0 d a:=by
        rw [permutationWindow_mem_iff]
        simp only [zero_add,pow_zero,Equiv.refl_apply]
        exact ⟨⟨j,by have hh:=Finset.mem_range.mp hj;omega⟩,rfl⟩
      exact Finset.disjoint_left.mp havoid hw' ho
    have hi0:i=0:=Fin.ext (by simpa using hzero)
    subst i
    exact ⟨hj,W,hW,hsp.1,hi⟩
  · rintro ⟨hj,W,hW,hh,hi⟩
    refine ⟨hj,W,hW,?_⟩
    apply (markedWheelPhysicalResources_spoke W ((π^j) a) hub).mpr
    exact ⟨hh,Finset.mem_image.mpr ⟨0,Finset.mem_univ _,hi⟩⟩
end Oberwolfach
