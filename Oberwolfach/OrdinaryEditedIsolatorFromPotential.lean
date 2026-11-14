module

public import Oberwolfach.OrdinaryIsolatorPotentialForcedRoot
public import Oberwolfach.OrdinaryConfigurationMonotone
public import Oberwolfach.IsolatorDeletionStability

@[expose] public section
/-! Root-omitted potential yields isolator counts in the edited parent,
even for an edge added by the edit. The extra forced root is charged in
the explicit deletion-degree bound. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 2048
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_edited_isolator_count_from_potential
    (P Q F:SimpleGraph V) (H₀ H:V→U→Prop) (k:ℕ) (hk:4≤k) (θ α β₀ β d:ℝ)
    (σ:Sym2 V→Bool) (hn:0<Fintype.card V) (hu:Fintype.card U≤Fintype.card V) (hQP:Q≤P\F)
    (hpotential:∀x y,Q.Adj x y→β₀≤ordinaryIsolatorPotential P F H₀ k θ α x y σ)
    (hD:∀x y,Q.Adj x y→∀v,
      (((retainedGraph P (Function.update σ s(x,y) true)\F)\Q).degree v:ℝ)≤d)
    (hEout:∀v,(∑u,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d)
    (hEin:∀u,(∑v,bipAdj (fun v u=>H₀ v u∧¬H v u) v u)≤d)
    (hsmall:8*d≤(β₀-β)*Fintype.card V):
    ∀x y,Q.Adj x y→β*(Fintype.card V:ℝ)^(k-1)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ):=by
  intro x y hxy
  let G:SimpleGraph V:=retainedGraph P (Function.update σ s(x,y) true)\F
  let D:SimpleGraph V:=G\Q
  let E:V→U→Prop:=fun v u=>H₀ v u∧¬H v u
  letI : DecidableRel D.Adj:=Classical.decRel _
  have hP:P.Adj x y:=(hQP hxy).1
  have hG:G.Adj x y:=⟨⟨hP,by simp⟩,(hQP hxy).2⟩
  have hroot:¬D.Adj x y:=by intro h;exact h.2 hxy
  have hp:=ordinary_isolator_potential_count_with_forced_root P F H₀ k (by omega) θ α β₀ x y σ hn hP (hpotential x y hxy)
  have hD':∀v,(D.degree v:ℝ)≤d:=by
    convert hD x y hxy using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
  have hloss:=ordinary_isolator_deletion_stability (P:=P) (Q:=G) (F:=F) (H:=H₀)
    (k:=k) (θ:=θ) (α:=α) hxy.ne hk hn hu D E d hD' hEout hEin hroot
  have hsub:G\D≤Q:=by
    intro v w hvw
    by_contra hnq
    exact hvw.2 ⟨hvw.1,hnq⟩
  have hsp:∀v u,(H₀ v u∧¬E v u)→H v u:=by
    intro v u hvu
    by_contra hh
    exact hvu.2 ⟨hvu.1,hh⟩
  have hmono:(Fintype.card (OrdinaryIsolatorConfiguration P (G\D) F (fun v u=>H₀ v u∧¬E v u) k θ α x y):ℝ)≤
      (Fintype.card (OrdinaryIsolatorConfiguration P Q F H k θ α x y):ℝ):=by
    exact_mod_cast ordinary_isolator_host_count_mono P (G\D) Q F (fun v u=>H₀ v u∧¬E v u) H k θ α x y hsub hsp
  have hpow:(Fintype.card V:ℝ)^(k-1)=(Fintype.card V:ℝ)^(k-2)*(Fintype.card V:ℝ):=by
    rw [←pow_succ];congr 1;omega
  have hsmall':8*d*(Fintype.card V:ℝ)^(k-2)≤(β₀-β)*(Fintype.card V:ℝ)^(k-1):=by
    rw [hpow]
    nlinarith only [mul_le_mul_of_nonneg_right hsmall (show 0≤(Fintype.card V:ℝ)^(k-2) by positivity)]
  change β₀*(Fintype.card V:ℝ)^(k-1)≤_ at hp
  change (_:ℝ)-_≤8*d*(Fintype.card V:ℝ)^(k-2) at hloss
  nlinarith only [hp,hloss,hsmall',hmono]
end Oberwolfach
