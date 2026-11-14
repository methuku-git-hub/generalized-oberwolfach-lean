module

public import Oberwolfach.LongRawMatchingHubPacking

@[expose] public section
/-! Reindex the ordinary wheels assigned to source cycles without changing
any rim label, sampled spoke or physical resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def reindexedOrdinaryWheel
    {V U A J:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (b:ℕ) (r:A→ℕ) (Q:∀a,OrderedOrdinaryWheel (U:=U) π b (r a))
    (n:J→ℕ) (select:J→A) (hlen:∀j,r (select j)=n j+1) (j:J):
    OrderedOrdinaryWheel (U:=U) π b (n j+1):=
  hlen j ▸ Q (select j)

@[simp] theorem cast_ordinary_wheel_hub
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    {π:Equiv.Perm V} {b r s:ℕ} (h:r=s) (Q:OrderedOrdinaryWheel (U:=U) π b r):
    ((h ▸ Q):OrderedOrdinaryWheel (U:=U) π b s).2=Q.2:=by cases h;rfl

@[simp] theorem cast_ordinary_wheel_vertex
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    {π:Equiv.Perm V} {b r s:ℕ} (h:r=s) (Q:OrderedOrdinaryWheel (U:=U) π b r) (i:Fin s):
    ((h ▸ Q):OrderedOrdinaryWheel (U:=U) π b s).1.val i=Q.1.val (Fin.cast h.symm i):=by cases h;rfl

@[simp] theorem cast_ordinary_wheel_resources
    {V U:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    {π:Equiv.Perm V} {b r s:ℕ} (h:r=s) (Q:OrderedOrdinaryWheel (U:=U) π b r):
    ordinaryWheelPhysicalResources ((h ▸ Q):OrderedOrdinaryWheel (U:=U) π b s)=ordinaryWheelPhysicalResources Q:=by cases h;rfl

@[simp] theorem cycleNext_cast {r s:ℕ} (h:r=s) (i:Fin s):
    Fin.cast h.symm (cycleNext i)=cycleNext (Fin.cast h.symm i):=by cases h;rfl

theorem assigned_ordinary_wheels_reindex
    {V U A J E L:Type} [Fintype V] [LinearOrder V] [Fintype U] [DecidableEq U]
    (π:Equiv.Perm V) (b m:ℕ) (tail head:E→V) (ktail khead:L→V) (H₀ Hₖ:V→U→Prop)
    (r:A→ℕ) (Q:∀a,OrderedOrdinaryWheel (U:=U) π b (r a)) (n:J→ℕ) (select:J↪A)
    (hlen:∀j,r (select j)=n j+1) (hub:U)
    (hhub:∀j,(Q (select j)).2=hub)
    (hspoke:∀a i,H₀ ((Q a).1.val i) (Q a).2)
    (R:V→V→Prop) (hdir:∀a i,R ((Q a).1.val i) ((Q a).1.val (cycleNext i)))
    (hpair:∀a a',a≠a'→Disjoint (ordinaryWheelPhysicalResources (Q a)) (ordinaryWheelPhysicalResources (Q a')))
    (M:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hcross:∀a W,W∈M→Disjoint (ordinaryWheelPhysicalResources (Q a)) (markedWheelPhysicalResources W)):
    let C:=reindexedOrdinaryWheel π b r Q n select hlen
    (∀j,(C j).2=hub) ∧ (∀j i,H₀ ((C j).1.val i) hub) ∧
    (∀j i,R ((C j).1.val i) ((C j).1.val (cycleNext i))) ∧
    (∀j j',j≠j'→Disjoint (ordinaryWheelPhysicalResources (C j)) (ordinaryWheelPhysicalResources (C j'))) ∧
    (∀j W,W∈M→Disjoint (ordinaryWheelPhysicalResources (C j)) (markedWheelPhysicalResources W)):=by
  intro C
  have hh:∀j,(C j).2=(Q (select j)).2:=by
    intro j
    exact cast_ordinary_wheel_hub (hlen j) (Q (select j))
  have hv:∀j i,(C j).1.val i=(Q (select j)).1.val (Fin.cast (hlen j).symm i):=by
    intro j i
    exact cast_ordinary_wheel_vertex (hlen j) (Q (select j)) i
  have hr:∀j,ordinaryWheelPhysicalResources (C j)=ordinaryWheelPhysicalResources (Q (select j)):=by
    intro j
    exact cast_ordinary_wheel_resources (hlen j) (Q (select j))
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro j;exact (hh j).trans (hhub j)
  · intro j i
    rw [hv j i,←hhub j]
    exact hspoke (select j) _
  · intro j i
    rw [hv j i,hv j (cycleNext i),cycleNext_cast (hlen j) i]
    exact hdir (select j) _
  · intro j k hne
    rw [hr j,hr k]
    exact hpair (select j) (select k) (fun he=>hne (select.injective he))
  · intro j W hW
    rw [hr j]
    exact hcross (select j) W hW
end Oberwolfach
