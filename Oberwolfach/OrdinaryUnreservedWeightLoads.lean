module

public import Oberwolfach.OrdinaryUnreservedDeletionBounds
public import Oberwolfach.OrdinaryRestrictedWeightLoads

@[expose] public section
/-! Fixed parent wheel weights restrict to the actual unreserved host, with
explicit loss in both rim and spoke loads. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_unreserved_weight_loads
    (Q F:SimpleGraph V) (H:V→U→Prop) (X:Finset V) (Z:Finset U) (R:SimpleGraph (V⊕U))
    (r:ℕ) (hr:3≤r) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (w:OrdinaryWheel Q F H r→ℝ) (bminus B ε₀ εstar ξ ζ:ℝ)
    (hb:0<bminus) (hB:0≤B) (hξ:0≤ξ) (hζ:0≤ζ)
    (hw:∀W,bminus/(Fintype.card V:ℝ)^(r-1)≤w W ∧ w W≤B/(Fintype.card V:ℝ)^(r-1))
    (hRim:∀x y,Q.Adj x y→|ordinaryRimLoad w x y-1|≤ε₀)
    (hSpoke:∀v u,H v u→|ordinarySpokeLoad w v u-1|≤ε₀)
    (hX:(X.card:ℝ)≤ξ*Fintype.card V) (hZ:(Z.card:ℝ)≤ξ*Fintype.card V)
    (hR:∀a,(R.degree a:ℝ)≤ζ*Fintype.card V)
    (hmargin:ε₀+8*(r:ℝ)^4*B*(ξ+ζ)≤εstar):
    ∃w':OrdinaryWheel (ordinaryUnreservedRim Q X R) F (ordinaryUnreservedSpokes H X Z R) r→ℝ,
      (∀W,bminus/(Fintype.card V:ℝ)^(r-1)≤w' W ∧ w' W≤B/(Fintype.card V:ℝ)^(r-1)) ∧
      (∀x y,(ordinaryUnreservedRim Q X R).Adj x y→|ordinaryRimLoad w' x y-1|≤εstar) ∧
      (∀v u,ordinaryUnreservedSpokes H X Z R v u→|ordinarySpokeLoad w' v u-1|≤εstar):=by
  let D:=ordinaryUnreservedRimDeletion Q X R
  let E:=ordinaryUnreservedSpokeDeletion X Z R
  let d:ℝ:=(ξ+ζ)*Fintype.card V
  have hd:0≤d:=by dsimp [d];positivity
  have hbnd:=ordinary_unreserved_deletion_degree_bounds Q X Z R ξ ζ hX hZ hR
  have hEout:∀v,(∑u,bipAdj E v u)≤d:=by
    intro v;simpa [bipAdj,Finset.sum_boole,d,E] using hbnd.2.1 v
  have hEin:∀u,(∑v,bipAdj E v u)≤d:=by
    intro u;simpa [bipAdj,Finset.sum_boole,d,E] using hbnd.2.2 u
  have hmargin':ε₀+8*(r:ℝ)^4*B*d/Fintype.card V≤εstar:=by
    have hn0:(Fintype.card V:ℝ)≠0:=by exact_mod_cast Nat.ne_of_gt hn
    have he:8*(r:ℝ)^4*B*d/Fintype.card V=8*(r:ℝ)^4*B*(ξ+ζ):=by
      dsimp [d];field_simp
    rw [he];exact hmargin
  have hh:=ordinary_restricted_weight_loads_from_parent Q F D H E r hr hn hu w bminus B d ε₀ εstar
    hb hB hd hw hbnd.1 hEout hEin hRim hSpoke hmargin'
  have he:=ordinary_unreserved_as_deletion Q H X Z R
  rw [he.1,he.2]
  exact hh
end Oberwolfach
