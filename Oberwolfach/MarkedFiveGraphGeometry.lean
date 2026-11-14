module

public import Oberwolfach.MarkedResourceExclusions
public import Oberwolfach.OrdinaryFiveGraphGeometry

@[expose] public section

/-! The physical resources of the five marked host graphs are disjoint.
Their auxiliary row and hub supports lie in the same finite unions. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 22000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {VL UL VR UR V U E K A S:Type}
    [Fintype VL] [Fintype UL] [Fintype VR] [Fintype UR] [Fintype A] [Fintype S]
    [DecidableEq V] [DecidableEq U]
    {Vm Um:Fin 3→Type} [∀ i,Fintype (Vm i)] [∀ i,Fintype (Um i)]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b:ℕ}

theorem marked_five_graph_geometry
    {Gleft:IndexedMarkedGraph VL UL A S} {Gright:IndexedMarkedGraph VR UR A S}
    {Gm:∀ i,IndexedMarkedGraph (Vm i) (Um i) A S}
    (L:IndexedMarkedHostRealization Gleft tail head ktail khead H₀ HK π b)
    (R:IndexedMarkedHostRealization Gright tail head ktail khead H₀ HK π b)
    (T:∀ i,IndexedMarkedHostRealization (Gm i) tail head ktail khead H₀ HK π b)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hLR:Disjoint L.rowSet R.rowSet)
    (hLT:∀ i,Disjoint L.rowSet (T i).rowSet)
    (hRT:∀ i,Disjoint R.rowSet (T i).rowSet)
    (hTT:∀ i j,i≠j→Disjoint (T i).rowSet (T j).rowSet):
    let D:Fin 5→Finset (Finset V⊕(V×U)):=![L.resources,(T 0).resources,(T 1).resources,(T 2).resources,R.resources]
    let X:=ordinaryFiveUnion L.rowSet R.rowSet (fun i=>(T i).rowSet)
    let B:=ordinaryFiveUnion L.hubSet R.hubSet (fun i=>(T i).hubSet)
    (∀ i j,i≠j→Disjoint (D i) (D j))∧
    ∀ i,∀ e∈D i,MarkedOldResource tail head ktail khead π X B e:=by
  dsimp only
  have hLR':=L.resources_disjoint R hp hLR
  have hLT' (i:Fin 3):=L.resources_disjoint (T i) hp (hLT i)
  have hRT' (i:Fin 3):=R.resources_disjoint (T i) hp (hRT i)
  have hTT' (i j:Fin 3) (hij:i≠j):=(T i).resources_disjoint (T j) hp (hTT i j hij)
  constructor
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    · exact (hij rfl).elim
    · exact hLT' 0
    · exact hLT' 1
    · exact hLT' 2
    · exact hLR'
    · exact (hLT' 0).symm
    · exact (hij rfl).elim
    · exact hTT' 0 1 (by decide)
    · exact hTT' 0 2 (by decide)
    · exact (hRT' 0).symm
    · exact (hLT' 1).symm
    · exact hTT' 1 0 (by decide)
    · exact (hij rfl).elim
    · exact hTT' 1 2 (by decide)
    · exact (hRT' 1).symm
    · exact (hLT' 2).symm
    · exact hTT' 2 0 (by decide)
    · exact hTT' 2 1 (by decide)
    · exact (hij rfl).elim
    · exact (hRT' 2).symm
    · exact hLR'.symm
    · exact hRT' 0
    · exact hRT' 1
    · exact hRT' 2
    · exact (hij rfl).elim
  · have hL:∀ e∈L.resources,MarkedOldResource tail head ktail khead π
        (ordinaryFiveUnion L.rowSet R.rowSet (fun i=>(T i).rowSet))
        (ordinaryFiveUnion L.hubSet R.hubSet (fun i=>(T i).hubSet)) e:=
      fun e he=>marked_old_resource_mono (ordinaryFiveUnion_left _ _ _) (ordinaryFiveUnion_left _ _ _) e (L.resources_supported e he).1
    have hR:∀ e∈R.resources,MarkedOldResource tail head ktail khead π
        (ordinaryFiveUnion L.rowSet R.rowSet (fun i=>(T i).rowSet))
        (ordinaryFiveUnion L.hubSet R.hubSet (fun i=>(T i).hubSet)) e:=
      fun e he=>marked_old_resource_mono (ordinaryFiveUnion_right _ _ _) (ordinaryFiveUnion_right _ _ _) e (R.resources_supported e he).1
    have hT:∀ i,∀ e∈(T i).resources,MarkedOldResource tail head ktail khead π
        (ordinaryFiveUnion L.rowSet R.rowSet (fun i=>(T i).rowSet))
        (ordinaryFiveUnion L.hubSet R.hubSet (fun i=>(T i).hubSet)) e:=
      fun i e he=>marked_old_resource_mono (ordinaryFiveUnion_mid _ _ _ i) (ordinaryFiveUnion_mid _ _ _ i) e ((T i).resources_supported e he).1
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons]
    · exact hL
    · exact hT 0
    · exact hT 1
    · exact hT 2
    · exact hR

end Oberwolfach
