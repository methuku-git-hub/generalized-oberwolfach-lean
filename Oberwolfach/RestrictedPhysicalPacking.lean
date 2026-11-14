module

public import Oberwolfach.DirectedArcsFromPhysicalPacking

@[expose] public section
/-! A restricted family is physically packed when its edges are covered by
an already packed old family and a disjointly packed new family. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem restricted_physical_packing_from_old_and_new
    {U V:Type*} [DecidableEq V]
    (remaining old new:U→Finset (Sym2 V)) (Pack:Finset (Sym2 V))
    (hcover:∀i,remaining i⊆old i∪new i)
    (hold:∀i j,i≠j→Disjoint (old i) (old j))
    (holdPack:∀i,old i⊆Pack)
    (hnew:∀i j,i≠j→Disjoint (new i) (new j))
    (hnewPack:∀i,Disjoint (new i) Pack):
    ∀i j,i≠j→Disjoint (remaining i) (remaining j):=by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro e hi hj
  rcases Finset.mem_union.mp (hcover i hi) with hiold | hinew
  · rcases Finset.mem_union.mp (hcover j hj) with hjold | hjnew
    · exact Finset.disjoint_left.mp (hold i j hij) hiold hjold
    · exact Finset.disjoint_left.mp (hnewPack j) hjnew (holdPack i hiold)
  · rcases Finset.mem_union.mp (hcover j hj) with hjold | hjnew
    · exact Finset.disjoint_left.mp (hnewPack i) hinew (holdPack j hjold)
    · exact Finset.disjoint_left.mp (hnew i j hij) hinew hjnew
end Oberwolfach
