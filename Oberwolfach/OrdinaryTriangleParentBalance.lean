module

public import Oberwolfach.TriangleBalanceFromRegularity
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section
/-! Discharge the triangle row ratio uniformly from the original regular
host density identity and the number of hubs excluded from the active set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_triangle_parent_balance (P:SimpleGraph V) (B:Finset U)
    (pR pH D ε a ω p η:ℝ) (hn:0<Fintype.card V) (hω:0<ω) (hp:0<p)
    (hη:0≤η) (hε:0≤ε) (ha:0≤a) (hpR0:0≤pR) (hpR1:pR≤1)
    (hpH:p≤pH) (hpH1:pH≤1) (hB:ω*Fintype.card V≤(B.card:ℝ))
    (hmiss:(Fintype.card U:ℝ)-B.card≤a*Fintype.card V)
    (hnear:∀v,|(P.degree v:ℝ)-D|≤ε*Fintype.card V)
    (hidentity:pR*D=2*Fintype.card U*pH) (hscale:ε+2*a≤2*ω*p*η):
    ∀v,|pR*(P.neighborFinset v).card/(2*B.card*pH)-1|≤η:=by
  intro v
  have hBcard:(B.card:ℝ)≤Fintype.card U:=Nat.cast_le.mpr (Finset.card_le_univ B)
  have hh:=triangle_balance_from_regularity (Fintype.card V) (Fintype.card U) B.card D (P.degree v)
    pR pH ε a ω p η (Nat.cast_pos.mpr hn) hω hp hη hε ha hpR0 hpR1 hpH hpH1
    hB hBcard hmiss (hnear v) hidentity hscale
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh
end Oberwolfach
