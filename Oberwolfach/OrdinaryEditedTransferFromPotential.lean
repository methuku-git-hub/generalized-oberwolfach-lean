module

public import Oberwolfach.TransferSurvivalCounts
public import Oberwolfach.TransferDeletionStability
public import Oberwolfach.OrdinaryConfigurationMonotone

@[expose] public section
/-! Root-completed transfer potentials yield transfer counts after edits,
including newly added root spokes. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edited_transfer_count_from_potential
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (r:ℕ) (hr:3≤r) (β₀ β d:ℝ)
    (σ:Sym2 V→Bool) (hn:0<Fintype.card V) (hd:0≤d)
    (hpotential:∀v u u',u≠u'→β₀≤transferSurvivalSum r hr P F (transferRootCompletedSpokes H₀ v) v u u' σ)
    (hD:∀v,(((retainedGraph P σ\F)\Q).degree v:ℝ)≤d)
    (hEin:∀v u,(∑z,bipAdj (fun z a=>transferRootCompletedSpokes H₀ v z a∧¬H z a) z u)≤d)
    (hsmall:5*(r:ℝ)^4*d≤(β₀-β)*Fintype.card V):
    ∀v (i j:{u // H v u}),i.val≠j.val→β*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ):=by
  intro v i j hij
  let G:SimpleGraph V:=retainedGraph P σ\F
  let D:SimpleGraph V:=G\Q
  let Hplus:=transferRootCompletedSpokes H₀ v
  let E:V→U→Prop:=fun z a=>Hplus z a∧¬H z a
  letI : DecidableRel D.Adj:=Classical.decRel _
  have hD':∀z,(D.degree z:ℝ)≤d:=by
    convert hD using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hden:0<(Fintype.card V:ℝ)^(r^2):=by positivity
  have hpot:=hpotential v i.val j.val hij
  have heq:=transferSurvivalSum_card r hr P F Hplus v i.val j.val σ
  have hp₀:β₀*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr (retainedGraph P σ) F Hplus v i.val j.val):ℝ):=
    (le_div_iff₀ hden).mp (hpot.trans_eq heq)
  have hc:=Fintype.card_congr (transferDeleteConflictsEquiv r hr (retainedGraph P σ) F Hplus v i.val j.val)
  have hp:β₀*(Fintype.card V:ℝ)^(r^2)≤
      (Fintype.card (OrdinaryTransferConfiguration hr G F Hplus v i.val j.val):ℝ):=by
    exact hp₀.trans_eq (by exact_mod_cast hc)
  have hroot:¬E v i.val∧¬E v j.val:=⟨fun h=>h.2 i.property,fun h=>h.2 j.property⟩
  have hloss:=ordinary_transfer_deletion_stability (hr:=hr) (Q:=G) (F:=F) (H:=Hplus)
    (v:=v) (u:=i.val) (u':=j.val) D E d hd hn hD' (hEin v) hroot
  have hsub:G\D≤Q:=by
    intro a b hab
    by_contra hh
    exact hab.2 ⟨hab.1,hh⟩
  have hsp:∀z a,(Hplus z a∧¬E z a)→H z a:=by
    intro z a hh
    by_contra hna
    exact hh.2 ⟨hh.1,hna⟩
  have hmono:(Fintype.card (OrdinaryTransferConfiguration hr (G\D) F (fun z a=>Hplus z a∧¬E z a) v i.val j.val):ℝ)≤
      (Fintype.card (OrdinaryTransferConfiguration hr Q F H v i.val j.val):ℝ):=by
    exact_mod_cast ordinary_transfer_host_count_mono (G\D) Q F (fun z a=>Hplus z a∧¬E z a) H r hr v i.val j.val hsub hsp
  have hpow:(Fintype.card V:ℝ)^(r^2)=(Fintype.card V:ℝ)^(r^2-1)*(Fintype.card V:ℝ):=by
    rw [←pow_succ];congr 1
    have hh:0<r^2:=pow_pos (show 0<r by omega) _
    omega
  have hsmall':5*(r:ℝ)^4*d*(Fintype.card V:ℝ)^(r^2-1)≤(β₀-β)*(Fintype.card V:ℝ)^(r^2):=by
    rw [hpow]
    nlinarith only [mul_le_mul_of_nonneg_right hsmall (show 0≤(Fintype.card V:ℝ)^(r^2-1) by positivity)]
  change (_:ℝ)-_≤5*(r:ℝ)^4*d*(Fintype.card V:ℝ)^(r^2-1) at hloss
  nlinarith only [hp,hloss,hsmall',hmono]
end Oberwolfach
