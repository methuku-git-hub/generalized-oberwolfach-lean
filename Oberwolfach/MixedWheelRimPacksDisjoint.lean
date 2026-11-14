module

public import Oberwolfach.RawOrdinarySeedPhysicalResources

@[expose] public section
/-! Physical resource-disjoint mixed wheel families have disjoint sets of
rim edges, even when ordinary wheel lengths vary with the index. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E L:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
  {tail head:E→V} {ktail khead:L→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ Hₖ:V→U→Prop}

def mixedWheelRimPack {I:Type} [Fintype I] (r:I→ℕ)
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (Q:∀i,OrderedOrdinaryWheel (U:=U) π b (r i)):Finset (Finset V):=
  M.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1) ∪
    Finset.univ.biUnion (fun i=>Finset.univ.image (fun a:Fin (r i)=>{(Q i).1.val a,(Q i).1.val (cycleNext a)}))

theorem mixed_wheel_rim_packs_disjoint
    {I J:Type} [Fintype I] [Fintype J]
    (r:I→ℕ) (s:J→ℕ)
    (M N:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (Q:∀i,OrderedOrdinaryWheel (U:=U) π b (r i)) (T:∀j,OrderedOrdinaryWheel (U:=U) π b (s j))
    (hMM:∀W∈M,∀Z∈N,Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hMO:∀W∈M,∀j,Disjoint (markedWheelPhysicalResources W) (ordinaryWheelPhysicalResources (T j)))
    (hOM:∀i,∀Z∈N,Disjoint (ordinaryWheelPhysicalResources (Q i)) (markedWheelPhysicalResources Z))
    (hOO:∀i j,Disjoint (ordinaryWheelPhysicalResources (Q i)) (ordinaryWheelPhysicalResources (T j))):
    Disjoint (mixedWheelRimPack r M Q) (mixedWheelRimPack s N T) :=by
  apply Finset.disjoint_left.mpr
  intro e he hf
  simp only [mixedWheelRimPack,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_image] at he hf
  rcases he with ⟨W,hW,hWe⟩|⟨i,a,hi⟩
  · have hWmem:Sum.inl e∈markedWheelPhysicalResources W:=(markedWheelPhysicalResources_rim W e).2 hWe
    rcases hf with ⟨Z,hZ,hZe⟩|⟨j,a,hj⟩
    · exact Finset.disjoint_left.mp (hMM W hW Z hZ) hWmem ((markedWheelPhysicalResources_rim Z e).2 hZe)
    · have hTmem:Sum.inl e∈ordinaryWheelPhysicalResources (T j):=by
        rw [←hj]
        simp [ordinaryWheelPhysicalResources]
      exact Finset.disjoint_left.mp (hMO W hW j) hWmem hTmem
  · have hQmem:Sum.inl e∈ordinaryWheelPhysicalResources (Q i):=by
      rw [←hi]
      simp [ordinaryWheelPhysicalResources]
    rcases hf with ⟨Z,hZ,hZe⟩|⟨j,a',hj⟩
    · exact Finset.disjoint_left.mp (hOM i Z hZ) hQmem ((markedWheelPhysicalResources_rim Z e).2 hZe)
    · have hTmem:Sum.inl e∈ordinaryWheelPhysicalResources (T j):=by
        rw [←hj]
        simp [ordinaryWheelPhysicalResources]
      exact Finset.disjoint_left.mp (hOO i j) hQmem hTmem
end Oberwolfach
