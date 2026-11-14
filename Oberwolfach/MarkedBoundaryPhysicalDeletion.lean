module

public import Oberwolfach.MarkedBoundaryExtensionCounts
public import Oberwolfach.PhysicalSpokeDeletion
public import Oberwolfach.SupportedBernoulliFactor

@[expose] public section

/-! The boundary extension inequalities in the host after an arbitrary
physical deletion. Every lost rim or spoke is charged at its actual
endpoint; the deterministic loss is not scaled by a sampling probability. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop}

theorem marked_boundary_counts_after_spoke_deletion
    (X:Finset V) (c:ℝ) (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (J:V→U→Prop) (δ:ℝ) (hJ:∀ u,((Finset.univ.filter (fun v=>J v u)).card:ℝ)≤δ):
    MarkedBoundaryExtensionCounts tail head ktail khead
      (fun v u=>H₀ v u∧¬J v u) (fun v u=>HK v u∧¬J v u) X (c-δ):=by
  have hdel (P:V→Prop) (u:U):
      ((X.filter P).card:ℝ)-δ≤(X.filter (fun v=>P v∧¬J v u)).card:=by
    have hh:=finite_predicate_delete_two (fun v=>v∈X∧P v) (fun v=>J v u) (fun _=>False)
      δ 0 (hJ u) (by simp)
    have h₁:Finset.univ.filter (fun v=>v∈X∧P v)=X.filter P:=by ext v;simp
    have h₂:Finset.univ.filter (fun v=>(v∈X∧P v)∧¬J v u∧¬False)=
        X.filter (fun v=>P v∧¬J v u):=by ext v;simp [and_assoc]
    have hh':((Finset.univ.filter (fun v=>v∈X∧P v)).card:ℝ)-δ-0≤
        (Finset.univ.filter (fun v=>(v∈X∧P v)∧¬J v u∧¬False)).card:=by
      convert hh using 1 <;> congr!
    simpa only [h₁,h₂,sub_zero] using hh' 
  constructor
  · intro j x u
    have hq:c≤((X.filter (fun v=>markedArcPresent tail head ktail khead j x v∧
        (if j then HK v u else H₀ v u))).card:ℝ):=by
      convert Q.step j x u using 1 <;> congr!
    have hd:((X.filter (fun v=>markedArcPresent tail head ktail khead j x v∧
        (if j then HK v u else H₀ v u))).card:ℝ)-δ≤
        (X.filter (fun v=>(markedArcPresent tail head ktail khead j x v∧
          (if j then HK v u else H₀ v u))∧¬J v u)).card:=by
      convert hdel (fun v=>markedArcPresent tail head ktail khead j x v∧
        (if j then HK v u else H₀ v u)) u using 1 <;> congr!
    have hh: c-δ≤(X.filter (fun v=>(markedArcPresent tail head ktail khead j x v∧
          (if j then HK v u else H₀ v u))∧¬J v u)).card:=by linarith only [hq,hd]
    convert hh using 1
    congr 2
    ext v
    cases j <;> simp [and_assoc]
  · intro x y u hxy
    have hq:c≤((X.filter (fun v=>markedArcPresent tail head ktail khead false x v∧
        markedArcPresent tail head ktail khead false v y∧H₀ v u)).card:ℝ):=by
      convert Q.join x y u hxy using 1 <;> congr!
    have hd:((X.filter (fun v=>markedArcPresent tail head ktail khead false x v∧
        markedArcPresent tail head ktail khead false v y∧H₀ v u)).card:ℝ)-δ≤
        (X.filter (fun v=>(markedArcPresent tail head ktail khead false x v∧
          markedArcPresent tail head ktail khead false v y∧H₀ v u)∧¬J v u)).card:=by
      convert hdel (fun v=>markedArcPresent tail head ktail khead false x v∧
        markedArcPresent tail head ktail khead false v y∧H₀ v u) u using 1 <;> congr!
    have hh:c-δ≤(X.filter (fun v=>(markedArcPresent tail head ktail khead false x v∧
          markedArcPresent tail head ktail khead false v y∧H₀ v u)∧¬J v u)).card:=by linarith only [hq,hd]
    convert hh using 1
    congr 2
    ext v
    simp [and_assoc]

theorem marked_boundary_counts_after_physical_deletion
    (π:Equiv.Perm V) (X:Finset V) (c:ℝ)
    (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (D:SimpleGraph (V⊕U)) (δ:ℝ) (hδ:0≤δ) (hD:∀ z,(D.degree z:ℝ)≤δ):
    MarkedBoundaryExtensionCounts
      (fun e:{e:E // ¬D.Adj (Sum.inl (tail e)) (Sum.inl (head e))}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))}=>ktail e.val) (fun e=>khead e.val)
      (fun v u=>H₀ v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
      (fun v u=>HK v u∧¬D.Adj (Sum.inl v) (Sum.inr u)) X (c-3*δ):=by
  let G:=D.comap (Sum.inl:V→V⊕U)
  have hG:∀ v,(G.degree v:ℝ)≤δ:=by
    intro v
    have hh:((D.comap (Sum.inl:V→V⊕U)).degree v:ℝ)≤D.degree (Sum.inl v):=by
      exact_mod_cast graph_comap_degree_le D ⟨Sum.inl,Sum.inl_injective⟩ v
    exact hh.trans (by convert hD (Sum.inl v) using 1 <;> congr!)
  have hR:=marked_boundary_counts_after_rim_deletion π X c Q G δ hδ hG
  have hS:=marked_boundary_counts_after_spoke_deletion X (c-2*δ) hR
    (fun v u=>D.Adj (Sum.inl v) (Sum.inr u)) δ
    (fun u=>(Nat.cast_le.mpr (physical_spoke_deleted_col D u)).trans (hD _))
  convert hS using 1 <;> first | rfl | ring

end Oberwolfach
