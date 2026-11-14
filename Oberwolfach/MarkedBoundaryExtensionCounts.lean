module

public import Oberwolfach.MarkedPhysicalDeletionExtensions

@[expose] public section

/-! The two row intersections used for boundary paths, counted on the inner
set itself. Roots remain in the ambient type. In particular no complement
of the inner set is charged against these local lower bounds. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop}

structure MarkedBoundaryExtensionCounts (tail head:E→V) (ktail khead:K→V)
    (H₀ HK:V→U→Prop) (X:Finset V) (c:ℝ):Prop where
  step:∀ (j:Bool) (x:V) (u:U),c≤((X.filter (fun y=>
    markedArcPresent tail head ktail khead j x y∧(if j then HK y u else H₀ y u))).card:ℝ)
  join:∀ (x y:V) (u:U),x≠y→c≤((X.filter (fun z=>
    markedArcPresent tail head ktail khead false x z∧
    markedArcPresent tail head ktail khead false z y∧H₀ z u)).card:ℝ)

theorem marked_boundary_counts_after_rim_deletion (π:Equiv.Perm V) (X:Finset V) (c:ℝ)
    (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ x,(D.degree x:ℝ)≤δ):
    MarkedBoundaryExtensionCounts
      (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val)
      H₀ HK X (c-2*δ):=by
  have hout (j:Bool) (x:V):((Finset.univ.filter (fun y=>D.Adj x (if j then π y else y))).card:ℝ)≤δ:=by
    cases j
    · have hh:((Finset.univ.filter (fun y=>D.Adj x ((Equiv.refl V) y))).card:ℝ)≤δ:=by
        rw [physical_permuted_neighbours_card];exact hD x
      convert hh using 1 <;> congr!
    · simpa only [ite_true,physical_permuted_neighbours_card] using hD x
  have hin (x:V):((Finset.univ.filter (fun y=>D.Adj y x)).card:ℝ)≤δ:=by
    have he:Finset.univ.filter (fun y=>D.Adj y x)=D.neighborFinset x:=by
      ext y;simp only [Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset];exact D.adj_comm y x
    rw [he,SimpleGraph.card_neighborFinset_eq_degree];exact hD x
  constructor
  · intro j x u
    let P:=fun y=>y∈X∧markedArcPresent tail head ktail khead j x y∧(if j then HK y u else H₀ y u)
    have hh:=finite_predicate_delete_two P (fun y=>D.Adj x (if j then π y else y)) (fun _=>False)
      δ 0 (hout j x) (by simp)
    have hparent:c≤((Finset.univ.filter P).card:ℝ):=by
      have he:Finset.univ.filter P=X.filter (fun y=>markedArcPresent tail head ktail khead j x y∧(if j then HK y u else H₀ y u)):=by
        ext y;simp [P]
      rw [he];exact Q.step j x u
    have he:Finset.univ.filter (fun y=>P y∧¬D.Adj x (if j then π y else y)∧¬False)=
        X.filter (fun y=>markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) j x y∧
          (if j then HK y u else H₀ y u)):=by
      ext y;simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,marked_arc_physical_restriction];tauto
    calc
      c-2*δ≤((Finset.univ.filter P).card:ℝ)-δ-0:=by linarith only [hparent,hδ]
      _≤_:=by rw [←he];convert hh using 1 <;> congr!
  · intro x y u hxy
    let P:=fun z=>z∈X∧markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧H₀ z u
    have hh:=finite_predicate_delete_two P (fun z=>D.Adj x z) (fun z=>D.Adj z y) δ δ (hout false x) (hin y)
    have hparent:c≤((Finset.univ.filter P).card:ℝ):=by
      have he:Finset.univ.filter P=X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧H₀ z u):=by
        ext z;simp [P]
      rw [he];exact Q.join x y u hxy
    have he:Finset.univ.filter (fun z=>P z∧¬D.Adj x z∧¬D.Adj z y)=
        X.filter (fun z=>markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) false x z∧
          markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) false z y∧H₀ z u):=by
      ext z;simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,marked_arc_physical_restriction,
        Bool.false_eq_true,ite_false];tauto
    calc
      c-2*δ≤((Finset.univ.filter P).card:ℝ)-δ-δ:=by linarith only [hparent]
      _≤_:=by rw [←he];convert hh using 1 <;> congr!

end Oberwolfach
