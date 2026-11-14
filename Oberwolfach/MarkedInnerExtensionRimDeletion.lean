module

public import Oberwolfach.MarkedBoundaryExtensionCounts

@[expose] public section

/-! Both typed closing intersections survive deletion of physical rim
edges. The incoming marked loss is charged at the successor of its root;
the original inner domain and all spoke conditions stay fixed. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [DecidableEq V]

theorem marked_inner_extension_counts_after_rim_deletion
    (tail head:E→V) (ktail khead:K→V) (H₀ HK:V→U→Prop)
    (π:Equiv.Perm V) (X:Finset V) (u:U) (c:ℝ)
    (hstep:∀ j x,c≤((X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧
      (if j then HK z u else H₀ z u))).card:ℝ))
    (hjoin:∀ j x y,x≠(if j then π y else y)→c≤((X.filter (fun z=>
      markedArcPresent tail head ktail khead false x z∧
      markedArcPresent tail head ktail khead j z y∧H₀ z u)).card:ℝ))
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ x,(D.degree x:ℝ)≤δ):
    let E':={e:E//¬D.Adj (tail e) (head e)}
    let K':={e:K//¬D.Adj (ktail e) (π (khead e))}
    let t':=fun e:E'=>tail e.val
    let h':=fun e:E'=>head e.val
    let kt':=fun e:K'=>ktail e.val
    let kh':=fun e:K'=>khead e.val;
    (∀ j x,c-2*δ≤((X.filter (fun z=>markedArcPresent t' h' kt' kh' j x z∧
      (if j then HK z u else H₀ z u))).card:ℝ))∧
    (∀ j x y,x≠(if j then π y else y)→c-2*δ≤((X.filter (fun z=>
      markedArcPresent t' h' kt' kh' false x z∧markedArcPresent t' h' kt' kh' j z y∧H₀ z u)).card:ℝ)):=by
  intro E' K' t' h' kt' kh'
  have harc (j:Bool) (x y:V):markedArcPresent t' h' kt' kh' j x y↔
      markedArcPresent tail head ktail khead j x y∧¬D.Adj x (if j then π y else y):=
    marked_arc_physical_restriction D j x y
  have hout (j:Bool) (x:V):((Finset.univ.filter (fun z=>D.Adj x (if j then π z else z))).card:ℝ)≤δ:=by
    cases j
    · have h:((Finset.univ.filter (fun z=>D.Adj x ((Equiv.refl V) z))).card:ℝ)≤δ:=by
        rw [physical_permuted_neighbours_card];exact hD x
      convert h using 1 <;> congr!
    · simpa only [ite_true,physical_permuted_neighbours_card] using hD x
  have hin (y:V):((Finset.univ.filter (fun z=>D.Adj z y)).card:ℝ)≤δ:=by
    have he:Finset.univ.filter (fun z=>D.Adj z y)=D.neighborFinset y:=by
      ext z;simp only [Finset.mem_filter,Finset.mem_univ,true_and,SimpleGraph.mem_neighborFinset];exact D.adj_comm z y
    rw [he,SimpleGraph.card_neighborFinset_eq_degree];exact hD y
  constructor
  · intro j x
    let P:=fun z=>z∈X∧markedArcPresent tail head ktail khead j x z∧(if j then HK z u else H₀ z u)
    have hh:=finite_predicate_delete_two P (fun z=>D.Adj x (if j then π z else z)) (fun _=>False)
      δ 0 (hout j x) (by simp)
    have hp:c≤((Finset.univ.filter P).card:ℝ):=by
      have he:Finset.univ.filter P=X.filter (fun z=>markedArcPresent tail head ktail khead j x z∧(if j then HK z u else H₀ z u)):=by
        ext z;simp [P]
      rw [he];exact hstep j x
    have he:Finset.univ.filter (fun z=>P z∧¬D.Adj x (if j then π z else z)∧¬False)=
        X.filter (fun z=>markedArcPresent t' h' kt' kh' j x z∧(if j then HK z u else H₀ z u)):=by
      ext z;simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,harc];tauto
    calc
      c-2*δ≤((Finset.univ.filter P).card:ℝ)-δ-0:=by linarith only [hp,hδ]
      _≤_:=by rw [←he];convert hh using 1 <;> congr!
  · intro j x y hxy
    let P:=fun z=>z∈X∧markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead j z y∧H₀ z u
    have hh:=finite_predicate_delete_two P (fun z=>D.Adj x z) (fun z=>D.Adj z (if j then π y else y))
      δ δ (hout false x) (hin _)
    have hp:c≤((Finset.univ.filter P).card:ℝ):=by
      have he:Finset.univ.filter P=X.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead j z y∧H₀ z u):=by
        ext z;simp [P]
      rw [he];exact hjoin j x y hxy
    have he:Finset.univ.filter (fun z=>P z∧¬D.Adj x z∧¬D.Adj z (if j then π y else y))=
        X.filter (fun z=>markedArcPresent t' h' kt' kh' false x z∧markedArcPresent t' h' kt' kh' j z y∧H₀ z u):=by
      ext z;simp only [P,Finset.mem_filter,Finset.mem_univ,true_and,harc,Bool.false_eq_true,ite_false];tauto
    calc
      c-2*δ≤((Finset.univ.filter P).card:ℝ)-δ-δ:=by linarith only [hp]
      _≤_:=by rw [←he];convert hh using 1 <;> congr!
end Oberwolfach
