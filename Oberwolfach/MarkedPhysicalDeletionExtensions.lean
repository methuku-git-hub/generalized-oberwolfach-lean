module

public import Oberwolfach.MarkedHostExtensionCounts
public import Oberwolfach.MarkedPhysicalRimDeletionDegrees

@[expose] public section

/-! Actual marked extension intersections after a physical rim deletion.
An incoming marked constraint is charged at the successor of its root. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_arc_physical_restriction (D:SimpleGraph V) (j:Bool) (x y:V):
    markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) j x y↔
      markedArcPresent tail head ktail khead j x y∧¬D.Adj x (if j then π y else y):=by
  cases j <;> simp only [markedArcPresent,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    constructor
    · rintro ⟨e,ht,hh⟩
      exact ⟨⟨e.val,ht,hh⟩,by simpa only [ht,hh] using e.property⟩
    · rintro ⟨⟨e,ht,hh⟩,he⟩
      exact ⟨⟨e,by simpa only [ht,hh] using he⟩,ht,hh⟩

theorem finite_predicate_delete_two (P Q₁ Q₂:V→Prop) (d₁ d₂:ℝ)
    (h₁:((Finset.univ.filter Q₁).card:ℝ)≤d₁)
    (h₂:((Finset.univ.filter Q₂).card:ℝ)≤d₂):
    ((Finset.univ.filter P).card:ℝ)-d₁-d₂≤
      (Finset.univ.filter (fun v=>P v∧¬Q₁ v∧¬Q₂ v)).card:=by
  have hsub:Finset.univ.filter P⊆
      Finset.univ.filter (fun v=>P v∧¬Q₁ v∧¬Q₂ v)∪(Finset.univ.filter Q₁∪Finset.univ.filter Q₂):=by
    intro v hv
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union] at hv ⊢
    tauto
  have hn:((Finset.univ.filter P).card:ℝ)≤
      (Finset.univ.filter (fun v=>P v∧¬Q₁ v∧¬Q₂ v)).card+
      ((Finset.univ.filter Q₁).card+(Finset.univ.filter Q₂).card):=by
    exact_mod_cast (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left (Finset.card_union_le _ _) _))
  linarith

theorem physical_permuted_neighbours_card (D:SimpleGraph V) (ρ:Equiv.Perm V) (x:V):
    (Finset.univ.filter (fun y=>D.Adj x (ρ y))).card=D.degree x:=by
  have he:Finset.univ.filter (fun y=>D.Adj x (ρ y))=(D.neighborFinset x).image ρ.symm:=by
    ext y
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,SimpleGraph.mem_neighborFinset]
    constructor
    · intro h;exact ⟨ρ y,h,ρ.symm_apply_apply y⟩
    · rintro ⟨z,hz,rfl⟩;simpa using hz
  rw [he,Finset.card_image_of_injective _ ρ.symm.injective,SimpleGraph.card_neighborFinset_eq_degree]

theorem marked_host_extensions_after_rim_deletion
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (D:SimpleGraph V) (δ:ℝ) (hδ:0≤δ) (hD:∀ v,(D.degree v:ℝ)≤δ):
    MarkedHostExtensionCounts
      (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val)
      H₀ HK π b l (c-2*δ) ch:=by
  have hout (j:Bool) (x:V):((Finset.univ.filter (fun y=>D.Adj x (if j then π y else y))).card:ℝ)≤δ:=by
    cases j
    · have hh:((Finset.univ.filter (fun y=>D.Adj x ((Equiv.refl V) y))).card:ℝ)≤δ:=by
        rw [physical_permuted_neighbours_card];exact hD x
      convert hh using 1 <;> congr!
    · simpa only [ite_true,physical_permuted_neighbours_card] using hD x
  have hin (j:Bool) (x:V):((Finset.univ.filter (fun y=>D.Adj y (if j then π x else x))).card:ℝ)≤δ:=by
    have he:(Finset.univ.filter (fun y=>D.Adj y (if j then π x else x))).card=
        D.degree (if j then π x else x):=by
      have hset:Finset.univ.filter (fun y=>D.Adj y (if j then π x else x))=
          Finset.univ.filter (fun y=>D.Adj (if j then π x else x) ((Equiv.refl V) y)):=by
        ext y;simp only [Finset.mem_filter];rw [D.adj_comm];rfl
      rw [hset,physical_permuted_neighbours_card]
    rw [he];exact hD _
  have hnone:((Finset.univ.filter (fun _:V=>False)).card:ℝ)≤(0:ℝ):=by simp
  constructor
  · intro j k x P hP
    have hh:=finite_predicate_delete_two
      (fun y=>markedArcPresent tail head ktail khead j x y∧markedSpokesTo H₀ HK k P y)
      (fun y=>D.Adj x (if j then π y else y)) (fun _=>False) δ 0 (hout j x) (by simp)
    have he:Finset.univ.filter (fun y=>
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) j x y∧markedSpokesTo H₀ HK k P y)=
        Finset.univ.filter (fun y=>(markedArcPresent tail head ktail khead j x y∧markedSpokesTo H₀ HK k P y)∧
          ¬D.Adj x (if j then π y else y)∧¬False):=by
      ext y;simp only [Finset.mem_filter,marked_arc_physical_restriction];tauto
    rw [he]
    calc
      c-2*δ≤((Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead j x y∧markedSpokesTo H₀ HK k P y)).card:ℝ)-δ-0:=by
        have hq:c≤((Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead j x y∧markedSpokesTo H₀ HK k P y)).card:ℝ):=by
          convert Q.outgoing j k x P hP using 1 <;> congr!
        linarith only [hq,hδ]
      _≤_:=by convert hh using 1 <;> congr!
  · intro j k x P hP
    have hh:=finite_predicate_delete_two
      (fun y=>markedArcPresent tail head ktail khead j y x∧markedSpokesTo H₀ HK k P y)
      (fun y=>D.Adj y (if j then π x else x)) (fun _=>False) δ 0 (hin j x) (by simp)
    have he:Finset.univ.filter (fun y=>
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) j y x∧markedSpokesTo H₀ HK k P y)=
        Finset.univ.filter (fun y=>(markedArcPresent tail head ktail khead j y x∧markedSpokesTo H₀ HK k P y)∧
          ¬D.Adj y (if j then π x else x)∧¬False):=by
      ext y;simp only [Finset.mem_filter,marked_arc_physical_restriction];tauto
    rw [he]
    calc
      c-2*δ≤((Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead j y x∧markedSpokesTo H₀ HK k P y)).card:ℝ)-δ-0:=by
        have hq:c≤((Finset.univ.filter (fun y=>markedArcPresent tail head ktail khead j y x∧markedSpokesTo H₀ HK k P y)).card:ℝ):=by
          convert Q.incoming j k x P hP using 1 <;> congr!
        linarith only [hq,hδ]
      _≤_:=by convert hh using 1 <;> congr!
  · intro k x y P hxy hP
    have hh:=finite_predicate_delete_two
      (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false y z∧markedSpokesTo H₀ HK k P z)
      (fun z=>D.Adj x z) (fun z=>D.Adj y z) δ δ (hout false x) (hout false y)
    have he:Finset.univ.filter (fun z=>
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) false x z∧
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) false y z∧markedSpokesTo H₀ HK k P z)=
        Finset.univ.filter (fun z=>(markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false y z∧markedSpokesTo H₀ HK k P z)∧¬D.Adj x z∧¬D.Adj y z):=by
      ext z;simp only [Finset.mem_filter,marked_arc_physical_restriction,Bool.false_eq_true,ite_false];tauto
    rw [he]
    calc
      c-2*δ≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false y z∧markedSpokesTo H₀ HK k P z)).card:ℝ)-δ-δ:=by
        have hq:c≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false y z∧markedSpokesTo H₀ HK k P z)).card:ℝ):=by
          convert Q.twoOutgoing k x y P hxy hP using 1 <;> congr!
        linarith only [hq,hδ]
      _≤_:=by convert hh using 1 <;> congr!
  · intro j k x y P hxy hP
    have hh:=finite_predicate_delete_two
      (fun z=>markedArcPresent tail head ktail khead j z x∧markedArcPresent tail head ktail khead j z y∧markedSpokesTo H₀ HK k P z)
      (fun z=>D.Adj z (if j then π x else x)) (fun z=>D.Adj z (if j then π y else y)) δ δ (hin j x) (hin j y)
    have he:Finset.univ.filter (fun z=>
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) j z x∧
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) j z y∧markedSpokesTo H₀ HK k P z)=
        Finset.univ.filter (fun z=>(markedArcPresent tail head ktail khead j z x∧markedArcPresent tail head ktail khead j z y∧markedSpokesTo H₀ HK k P z)∧¬D.Adj z (if j then π x else x)∧¬D.Adj z (if j then π y else y)):=by
      ext z;simp only [Finset.mem_filter,marked_arc_physical_restriction];tauto
    rw [he]
    calc
      c-2*δ≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead j z x∧markedArcPresent tail head ktail khead j z y∧markedSpokesTo H₀ HK k P z)).card:ℝ)-δ-δ:=by
        have hq:c≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead j z x∧markedArcPresent tail head ktail khead j z y∧markedSpokesTo H₀ HK k P z)).card:ℝ):=by
          convert Q.twoIncoming j k x y P hxy hP using 1 <;> congr!
        linarith only [hq,hδ]
      _≤_:=by convert hh using 1 <;> congr!
  · intro k x y P hxy hP
    have hh:=finite_predicate_delete_two
      (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧markedSpokesTo H₀ HK k P z)
      (fun z=>D.Adj x z) (fun z=>D.Adj z y) δ δ (hout false x) (hin false y)
    have he:Finset.univ.filter (fun z=>
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) false x z∧
        markedArcPresent (fun e:{e:E // ¬D.Adj (tail e) (head e)}=>tail e.val) (fun e=>head e.val)
          (fun e:{e:K // ¬D.Adj (ktail e) (π (khead e))}=>ktail e.val) (fun e=>khead e.val) false z y∧markedSpokesTo H₀ HK k P z)=
        Finset.univ.filter (fun z=>(markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧markedSpokesTo H₀ HK k P z)∧¬D.Adj x z∧¬D.Adj z y):=by
      ext z;simp only [Finset.mem_filter,marked_arc_physical_restriction,Bool.false_eq_true,ite_false];tauto
    rw [he]
    calc
      c-2*δ≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧markedSpokesTo H₀ HK k P z)).card:ℝ)-δ-δ:=by
        have hq:c≤((Finset.univ.filter (fun z=>markedArcPresent tail head ktail khead false x z∧markedArcPresent tail head ktail khead false z y∧markedSpokesTo H₀ HK k P z)).card:ℝ):=by
          convert Q.twoStep k x y P hxy hP using 1 <;> congr!
        linarith only [hq,hδ]
      _≤_:=by convert hh using 1 <;> congr!
  · exact Q.hubs

end Oberwolfach
