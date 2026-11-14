module

public import Oberwolfach.OrdinaryUnreservedPackingCertificate
public import Oberwolfach.TypedMatrixRealization

@[expose] public section
/-! Restrict the original rim orientation to the actual unreserved graph;
no new orientation choices or edges are introduced. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

def ordinaryUnreservedOrientation (A:V→V→ℕ) (X:Finset V) (R:SimpleGraph (V⊕U)):V→V→ℕ:=
  fun x y=>if (x∈X∧y∈X)∨R.Adj (Sum.inl x) (Sum.inl y) then 0 else A x y

theorem ordinary_unreserved_orientation_graph
    (Q:SimpleGraph V) (A:V→V→ℕ) (X:Finset V) (R:SimpleGraph (V⊕U))
    (hA:∀x y,A x y+A y x=if Q.Adj x y then 1 else 0):
    ∀x y,ordinaryUnreservedOrientation A X R x y+ordinaryUnreservedOrientation A X R y x=
      if (ordinaryUnreservedRim Q X R).Adj x y then 1 else 0:=by
  intro x y
  have hh:=hA x y
  have hr:R.Adj (Sum.inl y) (Sum.inl x)↔R.Adj (Sum.inl x) (Sum.inl y):=R.adj_comm _ _
  by_cases hq:Q.Adj x y <;> by_cases hi:x∈X∧y∈X <;>
    by_cases hd:R.Adj (Sum.inl x) (Sum.inl y)
  all_goals simp [ordinaryUnreservedOrientation,ordinaryUnreservedRim,spanningRestriction_adj,
    SimpleGraph.sdiff_adj,hq,hi,hd,hr,and_comm] at *
  all_goals omega

theorem ordinary_orientation_is_indicator (Q:SimpleGraph V) (A:V→V→ℕ)
    (hA:∀x y,A x y+A y x=if Q.Adj x y then 1 else 0):
    A=relationMultiplicity (fun x y=>A x y=1):=by
  funext x y
  have hh:=hA x y
  by_cases he:A x y=1
  · simp [relationMultiplicity,he]
  · have hle:A x y≤1:=by split_ifs at hh <;> omega
    have hz:A x y=0:=by omega
    simp [relationMultiplicity,he,hz]

theorem ordinary_unreserved_orientation_indicator (Q:SimpleGraph V) (A:V→V→ℕ) (X:Finset V)
    (R:SimpleGraph (V⊕U)) (hA:∀x y,A x y+A y x=if Q.Adj x y then 1 else 0):
    ordinaryUnreservedOrientation A X R=
      relationMultiplicity (fun x y=>A x y=1∧¬(x∈X∧y∈X)∧¬R.Adj (Sum.inl x) (Sum.inl y)):=by
  funext x y
  have hh:=hA x y
  have hle:A x y≤1:=by split_ifs at hh <;> omega
  by_cases he:A x y=1 <;> by_cases hi:x∈X∧y∈X <;> by_cases hd:R.Adj (Sum.inl x) (Sum.inl y)
  all_goals simp [ordinaryUnreservedOrientation,relationMultiplicity,he,hi,hd]
  all_goals omega
end Oberwolfach
