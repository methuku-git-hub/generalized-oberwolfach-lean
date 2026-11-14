module

public import Oberwolfach.MarkedWheelResources
public import Oberwolfach.MarkedSingleWheelWalk

@[expose] public section
/-! A path whose edges are covered by disjoint wheel rims and whose length is
the sum of the rim sizes uses every edge of every wheel. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem sym2_toFinset_injective_local {V:Type} [DecidableEq V]:Function.Injective (Sym2.toFinset : Sym2 V→Finset V):=by
  intro x y h
  induction x using Sym2.ind with
  | _ a b =>
    induction y using Sym2.ind with
    | _ c d =>
      simp only [Sym2.toFinset_mk_eq] at h
      have ha:a=c∨a=d:=by
        have hh:a∈({c,d}:Finset V):=h ▸ (by simp)
        simpa using hh
      have hb:b=c∨b=d:=by
        have hh:b∈({c,d}:Finset V):=h ▸ (by simp)
        simpa using hh
      have hc:c=a∨c=b:=by
        have hh:c∈({a,b}:Finset V):=h.symm ▸ (by simp)
        simpa using hh
      have hd:d=a∨d=b:=by
        have hh:d∈({a,b}:Finset V):=h.symm ▸ (by simp)
        simpa using hh
      apply Sym2.eq_iff.mpr
      rcases ha with ha|ha <;> rcases hb with hb|hb <;> rcases hc with hc|hc <;> rcases hd with hd|hd <;> subst_vars <;> simp

theorem wheel_run_physical_edges_saturate
    {V U E K I:Type} [Fintype V] [DecidableEq V] [DecidableEq U] [Fintype I] [DecidableEq I]
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V) (m b:ℕ) (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (W:I→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hp:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (hdis:∀i j,i≠j→Disjoint (markedWheelPhysicalResources (W i)) (markedWheelPhysicalResources (W j)))
    {a z:V} (q:G.Walk a z) (hq:q.IsPath) (hlen:q.length=Fintype.card I*(m+1))
    (hcover:∀e∈q.edges,∃i,e.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W i).1):
    (q.edges.toFinset.image Sym2.toFinset)=Finset.univ.biUnion (fun i=>markedCyclePhysicalEdges tail head ktail khead m π b (W i).1):=by
  let Rim:=fun i=>markedCyclePhysicalEdges tail head ktail khead m π b (W i).1
  have hd:(↑(Finset.univ:Finset I):Set I).PairwiseDisjoint Rim:=by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    have h1:Sum.inl x∈markedWheelPhysicalResources (W i):=(markedWheelPhysicalResources_rim (W i) x).mpr hx
    have h2:Sum.inl x∈markedWheelPhysicalResources (W j):=(markedWheelPhysicalResources_rim (W j) x).mpr hy
    exact Finset.disjoint_left.mp (hdis i j hij) h1 h2
  have hrim:(Finset.univ.biUnion Rim).card=Fintype.card I*(m+1):=by
    rw [Finset.card_biUnion hd]
    simp only [Rim,markedCyclePhysicalEdges_card tail head ktail khead m π b hp,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    norm_cast
  have hqcard:(q.edges.toFinset.image Sym2.toFinset).card=q.length:=by
    rw [Finset.card_image_of_injective _ sym2_toFinset_injective_local, List.toFinset_card_of_nodup hq.isTrail.edges_nodup,SimpleGraph.Walk.length_edges]
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp he
    exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_univ _,(hcover x (List.mem_toFinset.mp hx)).choose_spec⟩
  · rw [hrim,hqcard,hlen]
end Oberwolfach
