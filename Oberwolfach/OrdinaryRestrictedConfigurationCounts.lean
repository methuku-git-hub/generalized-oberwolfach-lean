module

public import Oberwolfach.IsolatorDeletionStability
public import Oberwolfach.TransferDeletionStability

@[expose] public section
/-! Parent isolator and transfer counts remain positive on the actual
unreserved graph when the physical deletion budget fits their margins. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_restricted_configuration_counts
    (P Q F D:SimpleGraph V) (H E:V→U→Prop) (r k:ℕ) (hr:3≤r) (hk:4≤k)
    (θ α β₀ β d:ℝ) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V) (hd:0≤d)
    (hD:∀v,(D.degree v:ℝ)≤d) (hEout:∀v,(∑u,bipAdj E v u)≤d) (hEin:∀u,(∑v,bipAdj E v u)≤d)
    (hparentI:∀x y,Q.Adj x y→β₀*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ))
    (hparentT:∀v (i j:{u // H v u}),i.val≠j.val→β₀*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ))
    (hsmallI:8*d≤(β₀-β)*Fintype.card V)
    (hsmallT:5*(r:ℝ)^4*d≤(β₀-β)*Fintype.card V):
    (∀x y,(Q\D).Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P (Q\D) F (fun v u=>H v u∧¬E v u) k θ α x y):ℝ)) ∧
    (∀v (i j:{u // H v u∧¬E v u}),i.val≠j.val→β*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr (Q\D) F (fun v u=>H v u∧¬E v u) v i.val j.val):ℝ)):=by
  let n:=Fintype.card V
  have hnR:(0:ℝ)<n:=Nat.cast_pos.mpr hn
  constructor
  · intro x y hxy
    have hloss:=ordinary_isolator_deletion_stability (P:=P) (Q:=Q) (F:=F) (H:=H)
      (k:=k) (θ:=θ) (α:=α) hxy.1.ne hk hn hu D E d hD hEout hEin hxy.2
    have hpow:(n:ℝ)^(k-1)=(n:ℝ)^(k-2)*(n:ℝ):=by rw [←pow_succ];congr 1;omega
    have hsmall:8*d*(n:ℝ)^(k-2)≤(β₀-β)*(n:ℝ)^(k-1):=by
      rw [hpow]
      nlinarith only [mul_le_mul_of_nonneg_right hsmallI (show 0≤(n:ℝ)^(k-2) by positivity)]
    have hp:=hparentI x y hxy.1
    change β₀*(n:ℝ)^(k-1)≤_ at hp
    change (_:ℝ)-_≤8*d*(n:ℝ)^(k-2) at hloss
    nlinarith only [hp,hloss,hsmall]
  · intro v i j hne
    have hloss:=ordinary_transfer_deletion_stability (hr:=hr) (Q:=Q) (F:=F) (H:=H)
      (v:=v) (u:=i.val) (u':=j.val) D E d hd hn hD hEin ⟨i.property.2,j.property.2⟩
    have hpow:(n:ℝ)^(r^2)=(n:ℝ)^(r^2-1)*(n:ℝ):=by
      rw [←pow_succ];congr 1
      have hh:0<r^2:=pow_pos (show 0<r by omega) _
      omega
    have hsmall:5*(r:ℝ)^4*d*(n:ℝ)^(r^2-1)≤(β₀-β)*(n:ℝ)^(r^2):=by
      rw [hpow]
      nlinarith only [mul_le_mul_of_nonneg_right hsmallT (show 0≤(n:ℝ)^(r^2-1) by positivity)]
    have hp:=hparentT v ⟨i.val,i.property.1⟩ ⟨j.val,j.property.1⟩ hne
    change β₀*(n:ℝ)^(r^2)≤_ at hp
    change (_:ℝ)-_≤5*(r:ℝ)^4*d*(n:ℝ)^(r^2-1) at hloss
    nlinarith only [hp,hloss,hsmall]
end Oberwolfach
