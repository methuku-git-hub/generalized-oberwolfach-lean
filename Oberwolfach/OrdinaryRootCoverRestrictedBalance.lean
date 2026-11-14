module

public import Oberwolfach.OrdinaryRootCoverRemainderFacts
public import Oberwolfach.OrdinaryRootCoverNonrootData
public import Oberwolfach.OrdinaryRestrictedNearBalance

@[expose] public section
/-! The actual remainder after the root cover remains nearly balanced on
nonroot vertices and hubs, with an explicit root-set error. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_root_cover_restricted_balance (Q F:SimpleGraph V) (H:V→U→Prop)
    (X T:Finset V) (Z W:Finset U) (r:ℕ) (η ell:ℝ)
    (hbal:∀v,Q.degree v=2*(Finset.univ.filter (H v)).card)
    (hdiv:∀u,r∣(Finset.univ.filter (fun v=>H v u)).card)
    (A:OrdinaryRootCoverNonrootData Q F H X T Z W r η ell):
    let Vfree:=Finset.univ\T;let Ufree:=Finset.univ\W;
    let Q':=Q\A.rim;let H':=fun v u=>H v u∧¬A.spokes v u;
    ∀v:Vfree,|(((Q'.induce (Vfree:Set V)).degree v):ℝ)-
      2*(Finset.univ.filter (fun u:Ufree=>H' v.val u.val)).card|≤(T.card:ℝ)+2*W.card:=by
  intro Vfree Ufree Q' H'
  have hh:=ordinary_restricted_near_balance Q' H' T W (by
    convert (ordinary_root_cover_remainder_facts Q F H X T Z W r η ell hbal hdiv A.toOrdinaryRootCoverData).1 using 1 <;>
      congr! 10 <;> exact Subsingleton.elim _ _)
  convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
