module

public import Oberwolfach.OrdinaryProtectedCorrectionForbiddenZeroInner
public import Oberwolfach.OrdinaryEligibleHost

@[expose] public section
/-! The permutation-conflict graph has bounded degree independently of host
size, giving the protected local edit without a separate conflict assumption. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_correction_conflict_inner
    (R JQ:SimpleGraph V) (J JH:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (π:Equiv.Perm V) (b:ℕ) (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (hJQ:∀v∈Y,∀w∈Y,¬JQ.Adj v w)
    (hJH:∀v u,JH v u→¬(v∈Y ∧ u∈B))
    (havoid:Disjoint K (ordinaryRootResources Y B)):
    let F:=permutationConflictGraph π b;
    let V₁:=↥X;let U₁:=↥Z;
    let Q:=(R\F)\JQ;
    let H:=fun v u=>J v u∧¬JH v u;
    let R₁:=R.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤2*(b:ℝ):=by
  intro F V₁ U₁ Q H R₁ J₁ G₁ Hs₁
  have hF:∀v,(F.degree v:ℝ)≤2*(b:ℝ):=by
    intro v
    have hh:=permutationConflictGraph_degree_le π b v
    exact_mod_cast hh
  exact ordinary_protected_correction_forbidden_zero_inner R F JQ J JH K X Y Z B hXY hZB hJQ hJH havoid
    (2*(b:ℝ)) (by positivity) hF
end Oberwolfach
