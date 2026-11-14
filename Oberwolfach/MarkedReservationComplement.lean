module

public import Oberwolfach.MarkedCoverPackingAvoidance
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section

/-! A packing in the complement of the inner graph and sampled boundary
avoids every reserved resource. This is a property of its actual host,
not a maximum-degree assumption on the packing. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
  {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_boundary_rim_allowed_physical_congr (X:Finset V) (hX:∀ x,π x∈X↔x∈X)
    (σ:Sym2 (V⊕U)→Bool) (j j':Bool) (x y x' y':V)
    (he:(if j then ({x,π y}:Finset V) else {x,y})=(if j' then ({x',π y'}:Finset V) else {x',y'})):
    markedBoundaryRimAllowed π X σ j x y↔markedBoundaryRimAllowed π X σ j' x' y':=by
  let P:V→V→Prop:=fun a c=>(a∈X∧c∈X)∨((a∈X∨c∈X)∧σ s(Sum.inl a,Sum.inl c)=true)
  have hc (j:Bool) (a c:V):markedBoundaryRimAllowed π X σ j a c↔P a (if j then π c else c):=by
    cases j <;> simp only [markedBoundaryRimAllowed,P,Bool.false_eq_true,ite_false,ite_true,hX]
  rw [hc,hc]
  have he':({x,(if j then π y else y)}:Finset V)={x',(if j' then π y' else y')}:=by
    cases j <;> cases j' <;> exact he
  have hp:({x,(if j then π y else y)}:Set V)={x',(if j' then π y' else y')}:=by
    simpa only [Finset.coe_insert,Finset.coe_singleton] using congrArg (fun s:Finset V=>(s:Set V)) he'
  rcases Set.pair_eq_pair_iff.mp hp with ⟨h1,h2⟩|⟨h1,h2⟩
  · rw [h1,h2]
  · rw [h1,h2]
    simp only [P,and_comm,or_comm,Sym2.eq_swap]

theorem marked_reservation_complement_excludes (m b:ℕ) (X:Finset V) (Z:Finset U)
    (hX:∀ x,π x∈X↔x∈X) (σ:Sym2 (V⊕U)→Bool)
    (M:Finset (MarkedWheel
      (fun e:{e:E//¬markedBoundaryRimAllowed π X σ false (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K//¬markedBoundaryRimAllowed π X σ true (ktail e) (khead e)}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun x u=>H₀ x u∧¬markedBoundarySpokeAllowed X Z σ x u)
        (fun x u=>HK x u∧¬markedBoundarySpokeAllowed X Z σ x u))):
    (∀ j x y,markedBoundaryRimAllowed π X σ j x y→
      Sum.inl (if j then ({x,π y}:Finset V) else {x,y})∉M.biUnion markedWheelPhysicalResources)∧
    (∀ x u,markedBoundarySpokeAllowed X Z σ x u→Sum.inr (x,u)∉M.biUnion markedWheelPhysicalResources):=by
  constructor
  · intro j x y hallow he
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
    rw [markedWheelPhysicalResources_rim] at he
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp he
    simp only [Function.comp_apply] at hi
    generalize markedCycleTypedEdge _ _ _ _ m π b W.1 i=a at hi
    cases a with
    | inl a=>
      exact a.property ((marked_boundary_rim_allowed_physical_congr X hX σ false j
        (tail a.val) (head a.val) x y hi).mpr hallow)
    | inr a=>
      exact a.property ((marked_boundary_rim_allowed_physical_congr X hX σ true j
        (ktail a.val) (khead a.val) x y hi).mpr hallow)
  · intro x u hallow he
    obtain ⟨W,hW,he⟩:=Finset.mem_biUnion.mp he
    have hs:=markedWheelPhysicalResources_spoke_present W x u he
    exact hs.elim (fun h=>h.2 hallow) (fun h=>h.2 hallow)
end Oberwolfach
