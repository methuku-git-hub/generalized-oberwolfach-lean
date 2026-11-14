module

public import Oberwolfach.MarkedWheelSpokeLabelsDisjoint

@[expose] public section
/-! At a fixed hub, choose the actual packed marked wheel for every distinct
selected interval label, preserving the original physical resources. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_select_distinct_root_wheels
    {V U E K I:Type} [Fintype V] [DecidableEq V] [DecidableEq U]
    (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ)) (hub:U)
    (hpack:∀W∈M,∀Z∈M,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (root:I→V) (hinj:Function.Injective root)
    (hex:∀i,∃W∈M,W.2.val=hub ∧ W.1.val 0=root i):
    ∃W:I→MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      (∀i,W i∈M ∧ (W i).2.val=hub ∧ (W i).1.val 0=root i) ∧
      (∀i j,i≠j→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W j))):=by
  classical
  choose W hW using hex
  refine ⟨W,hW,?_⟩
  intro i j hij
  apply hpack (W i) (hW i).1 (W j) (hW j).1
  intro he
  apply hij
  apply hinj
  calc
    root i=(W i).1.val 0:=(hW i).2.2.symm
    _=(W j).1.val 0:=by rw [he]
    _=root j:=(hW j).2.2
end Oberwolfach
