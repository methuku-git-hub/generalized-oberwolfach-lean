module

public import Oberwolfach.OrdinaryBoundaryExtensionStability
public import Oberwolfach.RawOrdinaryRowEvent

@[expose] public section
/-! The original common-row sample supplies the linear parent extension
counts after the allowed physical rim and spoke-column edits. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U Γ Color:Type} [Fintype V] [Fintype U] [Fintype Γ] [Fintype Color]
  [DecidableEq V] [DecidableEq U]

theorem ordinary_boundary_parent_extensions_from_common_sample
    (P Q:SimpleGraph V) (H:V→U→Prop) (π:Equiv.Perm V) (d:ℕ) (X:Finset V)
    (pR pH γ t L β:ℝ) (hpR:0≤pR) (hpR1:pR≤1) (hpH:0≤pH) (hγ:0≤γ)
    (s:U→Color→ℝ) (j:Color) (σ:RawWheelOutcome V U Γ Color)
    (hs:∀u,s u j=pH)
    (hrows:RawOrdinaryRows P π d 2 X pR s j t σ)
    (hparent:∀a c,γ*X.card≤((common X {a,c} (fun x=>P.neighborFinset x)).card:ℝ))
    (hrim:∀v,((changed ((rawWheelGraph P σ).neighborFinset v) (Q.neighborFinset v)).card:ℝ)≤L)
    (hcol:∀u,((changed (Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))
      (Finset.univ.filter (fun v=>H v u))).card:ℝ)≤L)
    (hmargin:β*Fintype.card (V⊕U)+t+3*L≤pR^2*pH*γ*X.card):
    ∀a c u,β*Fintype.card (V⊕U)≤((X.filter (fun v=>Q.Adj a v∧Q.Adj v c∧H v u)).card:ℝ):=by
  intro a c u
  let S:Finset V:={a,c}
  have hSc:S.card≤2:=by
    dsimp [S]
    have hh:=Finset.card_insert_le a ({c}:Finset V)
    simpa using hh
  have hpow:pR^2≤pR^S.card:=pow_le_pow_of_le_one hpR hpR1 hSc
  have hraw:=hrows S {u} hSc (by simp)
  have he:common (common X S (fun x=>(rawWheelGraph P σ).neighborFinset x)) {u}
      (fun u=>Finset.univ.filter (fun v=>rawWheelSpokes π d σ j v u))=
      X.filter (fun v=>(rawWheelGraph P σ).Adj a v∧(rawWheelGraph P σ).Adj v c∧rawWheelSpokes π d σ j v u):=by
    ext v
    simp only [mem_common_iff,Finset.mem_filter,Finset.mem_univ,true_and,S,Finset.mem_insert,
      Finset.mem_singleton,forall_eq_or_imp,forall_eq,SimpleGraph.mem_neighborFinset]
    have hh: (rawWheelGraph P σ).Adj c v↔(rawWheelGraph P σ).Adj v c:=(rawWheelGraph P σ).adj_comm _ _
    tauto
  rw [he,Finset.prod_singleton,hs u] at hraw
  have hpS:0≤pR^S.card*pH:=mul_nonneg (pow_nonneg hpR _) hpH
  have hfactor:pR^2*pH≤pR^S.card*pH:=mul_le_mul_of_nonneg_right hpow hpH
  have hbase:0≤γ*(X.card:ℝ):=by positivity
  have hm:=mul_le_mul_of_nonneg_right hfactor hbase
  have hc:=mul_le_mul_of_nonneg_left (hparent a c) hpS
  have hst:=ordinary_boundary_extension_count_stability (rawWheelGraph P σ) Q
    (fun v u=>rawWheelSpokes π d σ j v u) H X a c u L (hrim a) (hrim c) (hcol u)
  have hrawlow:=(abs_lt.mp hraw).1
  have hstup:=(abs_le.mp hst).2
  dsimp only [S] at hc hm hrawlow
  nlinarith only [hm,hc,hrawlow,hstup,hmargin]
end Oberwolfach
