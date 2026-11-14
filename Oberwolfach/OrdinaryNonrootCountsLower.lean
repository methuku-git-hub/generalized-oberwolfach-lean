module

public import Oberwolfach.OrdinaryNonrootIsolatorTransfer
public import Oberwolfach.OrdinaryNonrootTransferCountTransfer

@[expose] public section
/-! Convert the explicit excluded-root losses into the count hypotheses
needed for near-balance packing on the induced domain. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [DecidableEq V] [Fintype U] [DecidableEq U]

theorem ordinary_nonroot_isolator_lower
    (P Q F:SimpleGraph V) (H:V→U→Prop) (k:ℕ) (θ α β βfree:ℝ)
    (T:Finset V) (W:Finset U) (hk:3≤k) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V)
    (hparent:∀x y,Q.Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ))
    (hbudget:βfree*(Fintype.card ↥(Finset.univ\T):ℝ)^(k-1)+
      ((T.card:ℝ)+W.card)*(Fintype.card V:ℝ)^(k-2)≤β*(Fintype.card V:ℝ)^(k-1)):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    ∀(x y:A),(Q.induce (A:Set V)).Adj x y→βfree*(Fintype.card A:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration (P.induce (A:Set V)) (Q.induce (A:Set V))
        (F.induce (A:Set V)) (fun (v:A) (u:B)=>H v.val u.val) k θ α x y):ℝ):=by
  intro A B x y hxy
  have hxy':x≠y:=hxy.ne
  have hl:=ordinary_nonroot_isolator_count_transfer P Q F H k θ α T W hk hn hu x y hxy'
  have hp:=hparent x.val y.val hxy
  linarith

theorem ordinary_nonroot_transfer_lower
    (Q F:SimpleGraph V) (H:V→U→Prop) (r:ℕ) (hr:3≤r) (β βfree:ℝ)
    (T:Finset V) (W:Finset U)
    (hparent:∀v u u',H v u→H v u'→u≠u'→β*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v u u'):ℝ))
    (hbudget:βfree*(Fintype.card ↥(Finset.univ\T):ℝ)^(r^2)+
      (T.card:ℝ)*(r:ℝ)^2*(Fintype.card V:ℝ)^(r^2-1)≤β*(Fintype.card V:ℝ)^(r^2)):
    let A:=Finset.univ\T;let B:=Finset.univ\W;
    ∀(v:A) (u u':B),H v.val u.val→H v.val u'.val→u≠u'→βfree*(Fintype.card A:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr (Q.induce (A:Set V)) (F.induce (A:Set V))
        (fun (z:A) (h:B)=>H z.val h.val) v u u'):ℝ):=by
  intro A B v u u' hU hU' huu'
  have huu':u.val≠u'.val:=by intro he;exact huu' (Subtype.ext he)
  have hl:=ordinary_nonroot_transfer_count_transfer Q F H r hr T W v u u'
  have hp:=hparent v.val u.val u'.val hU hU' huu'
  linarith
end Oberwolfach
