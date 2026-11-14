module

public import Oberwolfach.MarkedPackingResourceDetermination

@[expose] public section
/-! Physical resource equality preserves all three degree counts used by
the sampled cover-down hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K E' K':Type} [Fintype V] [Fintype U] [Fintype E] [Fintype K] [Fintype E'] [Fintype K']
  [LinearOrder V] [DecidableEq U] [DecidableEq E] [DecidableEq K] [DecidableEq E'] [DecidableEq K']
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {m b:ℕ} {H₀ HK:V→U→Prop}
  {tail' head':E'→V} {ktail' khead':K'→V} {π':Equiv.Perm V} {m' b':ℕ} {H₀' HK':V→U→Prop}
theorem marked_packing_resource_equality_degree_counts
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ HK))
    (N:Finset (MarkedWheel tail' head' ktail' khead' m' π' b' H₀' HK'))
    (he:M.biUnion markedWheelPhysicalResources=N.biUnion markedWheelPhysicalResources):
    (∀ x,(markedPackingRimGraph M).degree x=(markedPackingRimGraph N).degree x)∧
    (∀ x,(Finset.univ.filter (markedPackingSpokes M x)).card=(Finset.univ.filter (markedPackingSpokes N x)).card)∧
    (∀ u,(Finset.univ.filter (fun x=>markedPackingSpokes M x u)).card=
      (Finset.univ.filter (fun x=>markedPackingSpokes N x u)).card):=by
  obtain ⟨hr,hs⟩:=markedPackingResourceEquality_graphs M N he
  refine ⟨fun x=>congrArg (fun G:SimpleGraph V=>G.degree x) hr,?_,?_⟩
  · intro x
    congr 1
    ext u
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hs]
  · intro u
    congr 1
    ext x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hs]
end Oberwolfach
