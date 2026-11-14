module

public import Oberwolfach.UniformRootsSpokeHubTrade

@[expose] public section
/-! The exact signed trade and both conflict-aware wheel decompositions for
one prescribed pair of hubs. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def OrdinaryHubTradeCertificate {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]
    (Q F:SimpleGraph V) (H:V→U→Prop) (u u':U) (S T:Finset V) (r:ℕ):Prop:=
  ∃ R:SimpleGraph V,
  let Sp:V→U→Prop:=fun v z=>(v∈S∪T∧z=u)∨(v∈S∧z=u')
  let Sm:V→U→Prop:=fun v z=>(v∈S∪T∧z=u')∨(v∈S∧z=u);
  HasOrdinaryWheelDecomposition R Sp r ∧ HasOrdinaryWheelDecomposition R Sm r ∧
  HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R Sp) ∧
  HasResourceDecomposition (ordinaryWheelResources (P:=Q) (F:=F) (Hbase:=H) (r:=r)) (ordinaryHostResources R Sm) ∧
  R≤Q ∧ (∀ v w,R.Adj v w→v∈S∪T∧w∈S∪T) ∧
  (∀ v w,v∈T→w∈T→¬R.Adj v w) ∧
  (∀ v z,Sp v z→H v z) ∧ (∀ v z,Sm v z→H v z) ∧
  (∀ e:Sym2 V⊕(V×U),
    (if e∈ordinaryHostResources R Sp then (1:ℤ) else 0)-
    (if e∈ordinaryHostResources R Sm then 1 else 0)=
    (if e∈T.image (fun v=>Sum.inr (v,u)) then 1 else 0)-
    (if e∈T.image (fun v=>Sum.inr (v,u')) then 1 else 0))
end Oberwolfach
