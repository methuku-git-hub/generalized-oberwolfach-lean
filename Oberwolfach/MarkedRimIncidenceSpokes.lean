module

public import Oberwolfach.MarkedRawSpokeTypes
public import Oberwolfach.DirectedIncidenceSums

@[expose] public section

/-! Read the spoke type of an assigned rim-incidence hub at its original
root (or at the root image). Only marked incoming incidences have type K. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K A:Type} [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {π:Equiv.Perm V} {b:ℕ} {H₀ HK:V→U→Prop}
    {src dst:A→V}

 def markedIncidenceSpokeType (jr:A→Bool) {v:V}:DirectedIncidence src dst v→Bool
  | .inl e=>jr e.val
  | .inr _=>false

 theorem marked_rim_incidence_spoke_types (n:ℕ) (hn:2≤n)
    (f:V→V) (jr:A→Bool) (p:A→Fin (n+1)→V) (hub:A→U)
    (C:A→MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hC:∀ e i,(C e).1.val i=Fin.cons (α:=fun _=>V) (f (src e)) (Fin.cons (f (dst e)) (p e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hCh:∀ e,(C e).2.val=hub e):
    ∀ v,∀ z:DirectedIncidence src dst v,
      if markedIncidenceSpokeType jr z then HK (f v) (hub (directedIncidenceEdge z))
      else H₀ (f v) (hub (directedIncidenceEdge z)):=by
  intro v z
  cases z with
  | inl e=>
    have hh:= (marked_rim_wheel_root_spoke_types n hn (C e.val)
      (f (src e.val)) (f (dst e.val)) (p e.val) (jr e.val) (hC e.val)).2
    simpa only [markedIncidenceSpokeType,directedIncidenceEdge,Sum.elim_inl,Sum.elim_inr,hCh,e.property] using hh
  | inr e=>
    have hh:= (marked_rim_wheel_root_spoke_types n hn (C e.val)
      (f (src e.val)) (f (dst e.val)) (p e.val) (jr e.val) (hC e.val)).1
    simpa only [markedIncidenceSpokeType,directedIncidenceEdge,Sum.elim_inl,Sum.elim_inr,hCh,e.property,Bool.false_eq_true,ite_false] using hh

 theorem marked_assigned_incidence_spoke_types (n:ℕ) (hn:2≤n)
    (f:V→V) (jr:A→Bool) (p:A→Fin (n+1)→V) (hub:A→U)
    (C:A→MarkedWheel tail head ktail khead (n+2) π b H₀ HK)
    (hC:∀ e i,(C e).1.val i=Fin.cons (α:=fun _=>V) (f (src e)) (Fin.cons (f (dst e)) (p e))
      (canonicalMarkedRotation (if jr e then 0 else 3) i))
    (hCh:∀ e,(C e).2.val=hub e)
    (τ:∀ v,Equiv.Perm (DirectedIncidence src dst v))
    (jv:(Σ v,DirectedIncidence src dst v)→Bool)
    (hj:∀ z,jv z=markedIncidenceSpokeType jr (τ z.1 z.2)):
    ∀ z:Σ v,DirectedIncidence src dst v,
      if jv z then HK (f z.1) (hub (directedIncidenceEdge (τ z.1 z.2)))
      else H₀ (f z.1) (hub (directedIncidenceEdge (τ z.1 z.2))):=by
  intro z
  rw [hj]
  exact marked_rim_incidence_spoke_types n hn f jr p hub C hC hCh z.1 (τ z.1 z.2)

end Oberwolfach
