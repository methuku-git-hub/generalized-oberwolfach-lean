module

public import Oberwolfach.BoundaryPathCoverage

@[expose] public section

/-! Reindex boundary-path packing by the actual finite family of assigned
pairs, preserving its graphs, loads, and individual prescribed triples. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U I J:Type} [Fintype V] [Fintype U] [Fintype I] [Fintype J]
  [DecidableEq V] [DecidableEq U]

theorem univ_filter_card_reindex (e:I≃J) (p:J→Prop):
    (Finset.univ.filter (fun i=>p (e i))).card=(Finset.univ.filter p).card:=by
  simp only [Finset.card_filter]
  exact Fintype.sum_equiv e _ _ (fun _=>rfl)

theorem wheelFamilyRim_reindex {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (C:J→OrdinaryWheel Q F H r) (e:I≃J):wheelFamilyRim (fun i=>C (e i))=wheelFamilyRim C:=by
  ext a b
  simp only [wheelFamilyRim,SimpleGraph.iSup_adj]
  constructor
  · rintro ⟨i,hi⟩;exact ⟨e i,hi⟩
  · rintro ⟨j,hj⟩;obtain ⟨i,rfl⟩:=e.surjective j;exact ⟨i,hj⟩

theorem wheelFamilySpokes_reindex {Q F:SimpleGraph V} {H:V→U→Prop} {r:ℕ}
    (C:J→OrdinaryWheel Q F H r) (e:I≃J):wheelFamilySpokes (fun i=>C (e i))=wheelFamilySpokes C:=by
  funext a u
  apply propext
  constructor
  · rintro ⟨i,hi⟩;exact ⟨e i,hi⟩
  · rintro ⟨j,hj⟩;obtain ⟨i,rfl⟩:=e.surjective j;exact ⟨i,hj⟩

theorem indexed_boundary_path_wheel_packing (Q D₀ F:SimpleGraph V) (H E₀ R:V→U→Prop)
    (X:Finset V) (r K D:ℕ) (hr:4≤r) (hK:0<K)
    (x v w:I→V) (u:I→U) (hx:∀ i,x i∉X) (hv:∀ i,v i∈X) (hw:∀ i,w i∈X)
    (hvw:∀ i,v i≠w i) (hxv:∀ i,Q.Adj (x i) (v i)) (hxw:∀ i,Q.Adj (x i) (w i))
    (hDxv:∀ i,¬D₀.Adj (x i) (v i)) (hDxw:∀ i,¬D₀.Adj (x i) (w i))
    (hpair:∀ i j,i≠j→x i=x j→Disjoint ({v i,w i}:Finset V) {v j,w j})
    (hspoke:∀ i j,i≠j→u i=u j→Disjoint ({x i,v i,w i}:Finset V) {x j,v j,w j})
    (hroot:∀ i,∀ a∈({x i,v i,w i}:Finset V),H a (u i) ∧ ¬E₀ a (u i) ∧ R a (u i))
    (hFroot:∀ i,∀ a∈({x i,v i,w i}:Finset V),∀ c∈({x i,v i,w i}:Finset V),¬F.Adj a c)
    (hend:∀ a,(Finset.univ.filter (fun i=>a∈({x i,v i,w i}:Finset V))).card≤D)
    (hhub:∀ z,(Finset.univ.filter (fun i=>u i=z)).card≤D)
    (L d₀ e₀ s b:ℝ) (hL:0≤L) (hF:∀ a,(F.degree a:ℝ)≤L)
    (hD₀:∀ a∈X,(D₀.degree a:ℝ)≤d₀)
    (hE₀:∀ z,((Finset.univ.filter (fun a=>E₀ a z)).card:ℝ)≤e₀)
    (hR:∀ z,((Finset.univ.filter (fun a=>R a z)).card:ℝ)≤s)
    (hcount:∀ i,∀ a∈X,∀ c∈X,b≤(((X.filter (fun z=>H z (u i)))∩Q.neighborFinset a∩Q.neighborFinset c).card:ℝ))
    (hbudget:(Fintype.card I*r:ℕ)/(K:ℝ)+((r:ℝ)+3)*(L+1)+2*(d₀+2*(K+D:ℕ))+e₀+(D*r:ℕ)+s<b):
    ∃ C:I→OrdinaryWheel Q F H r,
      (∀ i,ordinaryWheelHub (C i)=u i ∧ (ordinaryWheelRim (C i)).Adj (x i) (v i) ∧
        (ordinaryWheelRim (C i)).Adj (x i) (w i) ∧
        (∀ a∈(ordinaryWheelRim (C i)).support,a=x i∨a∈X) ∧
        Disjoint (ordinaryWheelResources (C i)) (ordinaryHostResources D₀ E₀) ∧
        (∀ a∈(ordinaryWheelRim (C i)).support,R a (u i)→a∈({x i,v i,w i}:Finset V))) ∧
      (∀ i j,i≠j→Disjoint (ordinaryWheelResources (C i)) (ordinaryWheelResources (C j))) ∧
      (∀ a,boundaryWheelFreeLoad C x v w a≤K) ∧
      (∀ a,(wheelFamilyRim C).degree a≤2*(K+D)) ∧
      (∀ a,(Finset.univ.filter (fun z=>wheelFamilySpokes C a z)).card≤K+D) ∧
      (∀ z,(Finset.univ.filter (fun a=>wheelFamilySpokes C a z)).card≤D*r):=by
  let e:Fin (Fintype.card I)≃I:=(Fintype.equivFin I).symm
  obtain ⟨C,hC,hdis,hcap,hrim,hrow,hcol⟩:=boundary_path_wheel_packing Q D₀ F H E₀ R X
    (Fintype.card I) r K D hr hK (fun i=>x (e i)) (fun i=>v (e i)) (fun i=>w (e i))
    (fun i=>u (e i)) (fun i=>hx (e i)) (fun i=>hv (e i)) (fun i=>hw (e i))
    (fun i=>hvw (e i)) (fun i=>hxv (e i)) (fun i=>hxw (e i))
    (fun i=>hDxv (e i)) (fun i=>hDxw (e i))
    (fun i j hij he=>hpair (e i) (e j) (fun h=>hij (e.injective h)) he)
    (fun i j hij he=>hspoke (e i) (e j) (fun h=>hij (e.injective h)) he)
    (fun i=>hroot (e i)) (fun i=>hFroot (e i))
    (by
      intro a
      have he:(Finset.univ.filter (fun i=>a∈({x (e i),v (e i),w (e i)}:Finset V))).card=
          (Finset.univ.filter (fun i=>a∈({x i,v i,w i}:Finset V))).card:=by
        convert univ_filter_card_reindex e (fun i=>a∈({x i,v i,w i}:Finset V)) using 1
        all_goals congr 1;ext i;simp only [Finset.mem_filter]
      exact he.trans_le (hend a))
    (by
      intro z
      have he:(Finset.univ.filter (fun i=>u (e i)=z)).card=(Finset.univ.filter (fun i=>u i=z)).card:=by
        convert univ_filter_card_reindex e (fun i=>u i=z) using 1
        all_goals congr 1;ext i;simp only [Finset.mem_filter]
      exact he.trans_le (hhub z))
    L d₀ e₀ s b hL hF hD₀ hE₀ hR (fun i=>hcount (e i)) hbudget
  refine ⟨fun i=>C (e.symm i),?_,?_,?_,?_,?_,?_⟩
  · intro i;simpa only [e.apply_symm_apply] using hC (e.symm i)
  · intro i j hij
    exact hdis (e.symm i) (e.symm j) (fun he=>hij (e.symm.injective he))
  · intro a
    have hh:=hcap a
    unfold boundaryWheelFreeLoad at hh ⊢
    have heq:(Finset.univ.filter (fun i=>a∈rootWheelInternal (C (e.symm i)) (x i) (v i) (w i))).card=
        (Finset.univ.filter (fun i=>a∈rootWheelInternal (C i) (x (e i)) (v (e i)) (w (e i)))).card:=by
      convert univ_filter_card_reindex e.symm
        (fun i=>a∈rootWheelInternal (C i) (x (e i)) (v (e i)) (w (e i))) using 1
      all_goals congr 1;ext i;simp only [Finset.mem_filter,e.apply_symm_apply]
    rw [heq];exact hh
  · rw [wheelFamilyRim_reindex];exact hrim
  · rw [wheelFamilySpokes_reindex];exact hrow
  · rw [wheelFamilySpokes_reindex];exact hcol

end Oberwolfach
