module

public import Oberwolfach.OrdinarySparseProtectedWitness
public import Oberwolfach.OrdinaryProtectedCorrectionFromWitness
public import Oberwolfach.OrdinaryProtectedCorrectionCuts

@[expose] public section
/-! Apply the previously chosen uniform sparse-correction parameters to an
actual host, without deleting any edge of the protected inner pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem ordinary_protected_correction_at_order_modular
    (r:ℕ) (hr:3≤r) (ω h δ ξ:ℝ)
    (hω:0<ω) (hh:0<h) (hδ:0<δ) (hδsmall:δ<1/4)
    (hξ:0<ξ) (hξh:ξ≤h/100)
    (V U:Type) [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (η:ℝ) (hη:0≤η)
    (hηsmall:η≤(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).1)
    (hn:(ordinarySparseCorrectionParameters r hr ω h δ ξ hω hh hδ hδsmall hξ hξh).2≤Fintype.card V)
    (hnpos:0<Fintype.card V) (hωn:ω*Fintype.card V≤Fintype.card U)
    (hUn:Fintype.card U≤Fintype.card V)
    (Q:SimpleGraph V) (H:V→U→Prop) (R:V→V→Prop) (T:Finset V) (B:Finset U) (ζ:ℝ)
    (hζ:0≤ζ) (hζh:ζ≤h) (hT:(T.card:ℝ)≤ζ*Fintype.card V) (hB:(B.card:ℝ)≤ζ*Fintype.card U)
    (hOrient:∀x y,relationMultiplicity R x y+relationMultiplicity R y x=if Q.Adj x y then 1 else 0)
    (hcutR:BipartiteLargeCut (relationMultiplicity R) δ (2*h))
    (hcutH:BipartiteLargeCut (relationMultiplicity H) δ (2*h))
    (hbal:∀v,|(Q.degree v:ℝ)-2*(Finset.univ.filter (H v)).card|≤η*Fintype.card V):
    ∃(JQ:SimpleGraph V) (JH:V→U→Prop),
      JQ≤Q ∧ (∀v∈T,∀w∈T,¬JQ.Adj v w) ∧
      (∀v u,JH v u→H v u ∧ ¬(v∈T ∧ u∈B)) ∧
      (∀v,(Q\JQ).degree v=2*(Finset.univ.filter (fun u=>H v u ∧ ¬JH v u)).card) ∧
      (∀u,r∣(Finset.univ.filter (fun v=>H v u ∧ ¬JH v u)).card) ∧
      (∀v,(JQ.degree v:ℝ)+(Finset.univ.filter (JH v)).card≤10*ξ*Fintype.card V) ∧
      (∀u,((Finset.univ.filter (fun v=>JH v u)).card:ℝ)≤10*ξ*Fintype.card V):=by
  have hunpos:0<Fintype.card U:=by
    have hv:(0:ℝ)<(Fintype.card V:ℝ):=by exact_mod_cast hnpos
    have hu:0<(Fintype.card U:ℝ):=(mul_pos hω hv).trans_le hωn
    exact_mod_cast hu
  exact ordinary_protected_correction_from_witness r ξ δ h ζ Q H R T B hnpos hunpos hζ hζh hT hB hOrient hcutR hcutH
    (ordinary_sparse_protected_rectangle_witness r hr ω h δ ξ hω hh hδ hδsmall hξ hξh η hη hηsmall V U hn hωn hUn Q H R T B hbal)
end Oberwolfach
