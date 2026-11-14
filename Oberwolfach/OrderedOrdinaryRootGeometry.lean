module

public import Oberwolfach.OrderedOrdinaryWheelMarginal
public import Oberwolfach.CanonicalMarkedArcMembership

@[expose] public section
/-! Physical endpoints and hub forced by ordinary root incidences. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [LinearOrder V] [DecidableEq U]
  {r b:ℕ} {π:Equiv.Perm V}

theorem orderedOrdinary_rim_endpoints (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r) (x y:V)
    (h:Sum.inl (x,y)∈orderedOrdinaryResources W):
    x≠y ∧ x∈Set.range W.1.val ∧ y∈Set.range W.1.val:=by
  obtain ⟨i,hi⟩:=(orderedOrdinaryResources_rim W (x,y)).mp h
  have hx:W.1.val i=x:=congrArg Prod.fst hi
  have hy:W.1.val (cycleNext i)=y:=congrArg Prod.snd hi
  refine ⟨?_,⟨i,hx⟩,⟨cycleNext i,hy⟩⟩
  intro heq
  apply cycleNext_ne_self hr i
  exact (permutationSeparated_injective π b W.1.val W.1.property) (by rw [hx,hy,heq]) |>.symm

theorem orderedOrdinary_spoke_endpoint (W:OrderedOrdinaryWheel (U:=U) π b r) (v:V) (u:U)
    (h:Sum.inr (v,u)∈orderedOrdinaryResources W):
    v∈Set.range W.1.val ∧ W.2=u:=by
  obtain ⟨i,hi⟩:=(orderedOrdinaryResources_spoke W (v,u)).mp h
  exact ⟨⟨i,congrArg Prod.fst hi⟩,congrArg Prod.snd hi⟩

theorem orderedOrdinary_distinct_rims_physical (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r)
    (x y a c:V) (hxy:Sum.inl (x,y)∈orderedOrdinaryResources W)
    (hac:Sum.inl (a,c)∈orderedOrdinaryResources W) (hne:(x,y)≠(a,c)):
    s(x,y)≠s(a,c):=by
  obtain ⟨i,hi⟩:=(orderedOrdinaryResources_rim W (x,y)).mp hxy
  obtain ⟨j,hj⟩:=(orderedOrdinaryResources_rim W (a,c)).mp hac
  intro he
  have he':s(W.1.val i,W.1.val (cycleNext i))=s(W.1.val j,W.1.val (cycleNext j)):=by
    have hx:=congrArg Prod.fst hi
    have hy:=congrArg Prod.snd hi
    have ha:=congrArg Prod.fst hj
    have hc:=congrArg Prod.snd hj
    simp only [Prod.fst,Prod.snd] at hx hy ha hc
    rw [hx,hy,ha,hc]
    exact he
  have hij:=orderedOrdinaryPhysical_edge_injective hr W he'
  apply hne
  exact hi.symm.trans (hij ▸ hj)

theorem orderedOrdinary_two_rims_three_vertices (W:OrderedOrdinaryWheel (U:=U) π b r) (hr:3≤r)
    (x y a c:V) (hxy:Sum.inl (x,y)∈orderedOrdinaryResources W)
    (hac:Sum.inl (a,c)∈orderedOrdinaryResources W) (hne:(x,y)≠(a,c)):
    3≤({x,y,a,c}:Finset V).card:=by
  have h₁: x≠y:=(orderedOrdinary_rim_endpoints W hr x y hxy).1
  have h₂: a≠c:=(orderedOrdinary_rim_endpoints W hr a c hac).1
  have h₃:=orderedOrdinary_distinct_rims_physical W hr x y a c hxy hac hne
  exact (distinct_pair_union_card x y a c h₁ h₂ h₃).1
end Oberwolfach
