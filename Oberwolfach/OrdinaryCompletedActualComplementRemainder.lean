module

public import Oberwolfach.OrdinaryEmbeddedComplementsPhysicalUnion

@[expose] public section
/-! The actual edited-target remainder has the desired reference agreement
after the selected package's old and new factor edges cover the demand. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_completed_actual_complement_remainder {n q:ℕ}
    (F:Fin q→SimpleGraph (Fin n)) (C:∀u,Finset (F u).ConnectedComponent)
    (f:∀u,{x:Fin n // (F u).connectedComponentMk x∉C u}↪Fin n)
    (Old New:Fin q→Finset (Sym2 (Fin n)))
    (Target Sample Reference Protect Bad:SimpleGraph (Fin n)) (Inner:Finset (Fin n))
    (hRef:Reference≤Sample) (hProtect:Protect≤Reference) (hBad:Disjoint Reference Bad)
    (hInner:spanningRestriction Reference Inner≤Protect)
    (hTarget:∀v∈Inner,∀w∈Inner,Target.Adj v w↔Sample.Adj v w)
    (hAdj:∀u x y,((F u).induce {x | (F u).connectedComponentMk x∉C u}).Adj x y→
      (Target\Protect).Adj (f u x) (f u y))
    (hSplit:∀u,(((F u).induce {x | (F u).connectedComponentMk x∉C u}).edgeFinset).image (Sym2.map (f u))=Old u∪New u)
    (hCover:∀e∈(ordinaryPostmatchingRequired Target Sample Reference Bad (prescribedPhysicalUnion Old) Inner).edgeFinset,
      ∃u,e∈New u):
    let Rem:=Target\ordinaryEmbeddedComplements F C f;
    Rem≤Sample ∧ Disjoint Rem Bad ∧
      (∀v∈Inner,∀w∈Inner,Rem.Adj v w↔Reference.Adj v w) :=by
  intro Rem
  have hh:=ordinary_completed_factor_remainder
    (fun u=>(F u).induce {x | (F u).connectedComponentMk x∉C u}) (fun u=>f u) Old New
    Target Sample Reference Protect Bad Inner hRef hProtect hBad hInner hTarget hAdj hSplit hCover
  dsimp [Rem]
  rw [ordinary_embedded_complements_physical_union F C f]
  exact hh
end Oberwolfach
