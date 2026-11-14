module

public import Oberwolfach.OrdinaryInducedRawResource
public import Oberwolfach.OrdinaryRawMeanFactors

@[expose] public section
/-! On a fixed induced-domain wheel, the mapped ambient raw marginals have
constant rim and spoke probabilities. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Color : Type} [Fintype V] [Fintype U] [Fintype Color]
    [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_raw_marginal_on_candidate
    (P F : SimpleGraph V) (A : Set V) (u : U) (r : ℕ)
    (s : U → Color → ℝ) (j : Color) (pR pH : ℝ) (hs : s u j = pH)
    (W : OrdinaryWheel (P.induce A) (F.induce A) (fun _ : A => fun _ : Unit => True) r)
    (a : Sym2 A ⊕ (A × Unit)) (ha : a ∈ ordinaryWheelResources W) :
    rawWheelMarginal P (fun _ => pR) s j (ordinaryInducedRawResource A u a) =
      Sum.elim (fun _ => pR) (fun _ => pH) a := by
  cases a with
  | inl e =>
    have he := (ordinaryWheelResources_rim W e).mp ha
    induction e using Sym2.ind with
    | _ x y =>
      have hp : P.Adj x.val y.val := W.val.1.property he
      have hm : Sym2.map Subtype.val s(x,y) = s(x.val,y.val) := rfl
      simp only [ordinaryInducedRawResource, hm, rawWheelMarginal, SimpleGraph.mem_edgeSet,
        hp, ite_true, Sum.elim_inl]
  | inr a =>
    simp only [ordinaryInducedRawResource, rawWheelMarginal, Sum.elim_inr, hs]
end Oberwolfach
