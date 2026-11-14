module

public import Oberwolfach.WheelRunPhysicalEdgeSaturationLocal
public import Oberwolfach.ActualSelectedRunFamilyFromPacking

@[expose] public section
/-! Every selected wheel rim is present in its actual run: the disjoint rim
sizes exactly fill the run length. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem actual_run_wheel_edges_saturate_local
    {X V U E L K J:Type} [Fintype X] [DecidableEq X] [Fintype V] [LinearOrder V] [DecidableEq U] [DecidableEq K] [DecidableEq J]
    {F:SimpleGraph X} (data:ActualResidualData (K:=K) (J:=J) F)
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:L→V) (m b:ℕ) (hc:data.c=m+1)
    (π:Equiv.Perm V) (H₀ Hₖ:V→U→Prop)
    (W:actualSelectedSegmentIndex data→MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hm:2≤m) (hb:1≤b)
    (hpair:∀z z',z≠z'→Disjoint (markedWheelPhysicalResources (W z)) (markedWheelPhysicalResources (W z')))
    (r:SelectedRunIndex data.s₂ data.d data.T) {a z:V} (q:G.Walk a z) (hq:q.IsPath)
    (hlen:q.length=data.c*(r.2.val.2+1-r.2.val.1))
    (hcover:∀edge∈q.edges,∃z:actualSelectedSegmentIndex data,z.1=r ∧ edge.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W z).1):
    ∀z:actualSelectedSegmentIndex data,z.1=r→
      markedCyclePhysicalEdges tail head ktail khead m π b (W z).1⊆q.edges.toFinset.image Sym2.toFinset:=by
  let n:=r.2.val.2+1-r.2.val.1
  have hbounds:=actual_selected_run_bounds data r
  let Z:Fin n→actualSelectedSegmentIndex data:=fun i=>
    ⟨r,⟨⟨r.2.val.1+i.val,by have hi:=i.isLt;dsimp [n] at hi;omega⟩,by have hi:=i.isLt;dsimp [n] at hi;change r.2.val.1≤r.2.val.1+i.val ∧ r.2.val.1+i.val≤r.2.val.2;omega⟩⟩
  have hZinj:Function.Injective Z:=by
    intro i j h
    have hv:=congrArg (fun x:actualSelectedSegmentIndex data=>x.2.val.val) h
    apply Fin.ext
    dsimp [Z] at hv
    omega
  have hZsurj:∀z:actualSelectedSegmentIndex data,z.1=r→∃i:Fin n,Z i=z:=by
    rintro ⟨s,⟨j,hj⟩⟩ hs
    change s=r at hs
    subst s
    let i:Fin n:=⟨j.val-r.2.val.1,by dsimp [n];omega⟩
    refine ⟨i,?_⟩
    dsimp only [Z]
    congr 2
    apply Fin.ext
    dsimp [i]
    omega
  have hdis:∀i j:Fin n,i≠j→Disjoint (markedWheelPhysicalResources (W (Z i))) (markedWheelPhysicalResources (W (Z j))):=by
    intro i j hij
    exact hpair (Z i) (Z j) (fun he=>hij (hZinj he))
  have hlen':q.length=Fintype.card (Fin n)*(m+1):=by
    rw [Fintype.card_fin,hlen,hc]
    simp only [n,Nat.mul_comm]
  have hcover':∀edge∈q.edges,∃i:Fin n,edge.toFinset∈markedCyclePhysicalEdges tail head ktail khead m π b (W (Z i)).1:=by
    intro edge he
    obtain ⟨z,hzr,hmem⟩:=hcover edge he
    obtain ⟨i,hi⟩:=hZsurj z hzr
    exact ⟨i,hi ▸ hmem⟩
  have heq:=wheel_run_physical_edges_saturate_local G tail head ktail khead m b π H₀ Hₖ (fun i:Fin n=>W (Z i)) hm hb hdis q hq hlen' hcover'
  intro z hz edge he
  obtain ⟨i,hi⟩:=hZsurj z hz
  rw [heq]
  apply Finset.mem_biUnion.mpr
  refine ⟨i,Finset.mem_univ _,?_⟩
  simpa only [hi] using he
end Oberwolfach
