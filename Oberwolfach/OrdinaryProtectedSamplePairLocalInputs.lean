module

public import Oberwolfach.OrdinaryProtectedCorrectionWithForbiddenEdit

@[expose] public section
/-! Exact sample agreement on a protected pair supplies both local conflict
freedom and the physical edit bound for any actual host with a reserved set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]

theorem ordinary_protected_sample_pair_local_inputs
    (R F G:SimpleGraph V) (J H:V→U→Prop) (K:Finset (Sym2 V⊕(V×U)))
    (X Inner:Finset V) (Z Hubs:Finset U) (hX:X⊆Inner) (hZ:Z⊆Hubs)
    (hr:∀v∈Inner,∀w∈Inner,(R\F).Adj v w↔G.Adj v w)
    (hs:∀v∈Inner,∀u∈Hubs,J v u↔H v u)
    (hK:Disjoint K (ordinaryRootResources Inner Hubs)) (LF:ℝ) (hLF:0≤LF)
    (hF:∀v,(F.degree v:ℝ)≤LF):
    let S:=G\ordinaryResourceRim G K;let Hs:=fun v u=>H v u∧¬(Sum.inr (v,u)∈K);
    Disjoint (S.induce (X:Set V)) (F.induce (X:Set V)) ∧
    ∀a:↥X⊕↥Z,((changed
      ((ordinaryPhysicalGraph (R.induce (X:Set V)) (fun (v:↥X) (u:↥Z)=>J v.val u.val)).neighborFinset a)
      ((ordinaryPhysicalGraph (S.induce (X:Set V)) (fun (v:↥X) (u:↥Z)=>Hs v.val u.val)).neighborFinset a)).card:ℝ)≤LF :=by
  intro S Hs
  have hconf:Disjoint (S.induce (X:Set V)) (F.induce (X:Set V)):=by
    apply disjoint_iff_inf_le.mpr
    intro v w hvw
    have hg:G.Adj v.val w.val:=hvw.1.1
    have hf:F.Adj v.val w.val:=hvw.2
    exact ((hr v.val (hX v.property) w.val (hX w.property)).mpr hg).2 hf
  have hloc:=ordinary_protected_correction_forbidden_local_edit R F G J H
    (fun _ _=>False) K X Inner Z Hubs hX hZ hr (by intro v hv u hu _;exact hs v hv u hu)
    hK LF 0 hLF hF (by intro v;simp) (by intro u;simp)
  refine ⟨hconf,?_⟩
  intro a
  have hh:=hloc a
  simp only [add_zero] at hh
  convert hh using 1 <;> congr! 10 <;> exact Subsingleton.elim _ _
end Oberwolfach
