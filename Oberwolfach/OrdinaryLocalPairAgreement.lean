module

public import Oberwolfach.OrdinaryProtectedReservoirLocalAgreement

@[expose] public section
/-! Exact rim and spoke agreement on a protected pair gives zero local edit
on every smaller pair, including after reserving an avoiding resource set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_induced_physical_of_pair_agreement
    (R Q:SimpleGraph V) (J H:V→U→Prop) (X Y:Finset V) (Z B:Finset U)
    (hXY:X⊆Y) (hZB:Z⊆B)
    (hr:∀v∈Y,∀w∈Y,R.Adj v w↔Q.Adj v w)
    (hs:∀v∈Y,∀u∈B,J v u↔H v u):
    ordinaryPhysicalGraph (R.induce (X:Set V)) (fun (v:↥X) (u:↥Z)=>J v.val u.val)=
      ordinaryPhysicalGraph (Q.induce (X:Set V)) (fun (v:↥X) (u:↥Z)=>H v.val u.val):=by
  ext a b
  cases a with
  | inl v=>cases b with
    | inl w=>exact hr v.val (hXY v.property) w.val (hXY w.property)
    | inr u=>exact hs v.val (hXY v.property) u.val (hZB u.property)
  | inr u=>cases b with
    | inl v=>exact hs v.val (hXY v.property) u.val (hZB u.property)
    | inr z=>rfl

theorem ordinary_protected_reservoir_local_zero_edit
    (R Q:SimpleGraph V) (J H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Y:Finset V) (Z B:Finset U) (hXY:X⊆Y) (hZB:Z⊆B)
    (hr:∀v∈Y,∀w∈Y,R.Adj v w↔Q.Adj v w)
    (hs:∀v∈Y,∀u∈B,J v u↔H v u)
    (havoid:Disjoint K (ordinaryRootResources Y B)):
    let V₁:=↥X;let U₁:=↥Z;
    let R₁:=R.induce (X:Set V);
    let J₁:=fun (v:V₁) (u:U₁)=>J v.val u.val;
    let G₁:=(Q\ordinaryResourceRim Q K).induce (X:Set V);
    let Hs₁:=fun (v:V₁) (u:U₁)=>H v.val u.val∧¬(Sum.inr (v.val,u.val)∈K);
    ∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph G₁ Hs₁).neighborFinset a)).card:ℝ)≤0:=by
  intro V₁ U₁ R₁ J₁ G₁ Hs₁ a
  have he:=ordinary_induced_physical_of_pair_agreement R Q J H X Y Z B hXY hZB hr hs
  have hedit:∀a:V₁⊕U₁,((changed ((ordinaryPhysicalGraph R₁ J₁).neighborFinset a)
      ((ordinaryPhysicalGraph (Q.induce (X:Set V)) (fun (v:V₁) (u:U₁)=>H v.val u.val)).neighborFinset a)).card:ℝ)≤0:=by
    intro x
    have hn:(ordinaryPhysicalGraph R₁ J₁).neighborFinset x=
        (ordinaryPhysicalGraph (Q.induce (X:Set V)) (fun (v:V₁) (u:U₁)=>H v.val u.val)).neighborFinset x:=by
      ext y
      simp only [SimpleGraph.mem_neighborFinset]
      rw [he]
    rw [hn]
    simp [changed]
  have hh:=ordinary_protected_reservoir_local_reference R Q J H K X Y Z B hXY hZB havoid 0 hedit a
  convert hh using 1 <;> congr! 8 <;> exact Subsingleton.elim _ _
end Oberwolfach
