module

public import Oberwolfach.PrescribedExtraSaturationComponentBudgets
public import Oberwolfach.PrescribedFamilyFreeCycleRestrictedAdvance
public import Oberwolfach.PrescribedRestrictedLoadStep
public import Oberwolfach.PrescribedFamilyResources
public import Oberwolfach.PrescribedFamilyStateStep
public import Oberwolfach.PrescribedSourceComponentEdges
public import Oberwolfach.PrescribedComponentSourceEndpoints
public import Oberwolfach.PrescribedFreeComponentSteps

@[expose] public section
/-! Embed one actual source cycle with no prescribed vertex and update the complete family
state using only the original quantitative resources. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_family_free_cycle_restricted_advance_with_budget
    (st:PrescribedFamilyState I X V) (QV:I→Finset X) (Q:I→SimpleGraph X)
    (A₀:I→Finset X) (ψ:I→X→V) (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V)
    (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (k:I) (as:List X) (has:as.Nodup) (hlen:3≤as.length)
    (hfree:∀ x∈as,x∉st.assigned k) (hsubset:∀ x∈as,x∈QV k)
    (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X)
    (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (hsrc:DirectedCycleThrough Dsrc Fsrc as)
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β)
    (H:Finset I) (tLocal:ℝ) (Slocal:Finset V)
    (hLocal:∀v,(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)≤tLocal+1)
    (hSat:∀v,tLocal≤(((st.freeOccurrences.filter (fun p=>p.1∈H)).filter
      (fun p=>familyVertexImage st.vertexMap p=v)).card:ℝ)→v∈Slocal)
    (hδstrong:δ≤(β/200)^2) (hnstrong:200/β≤(Fintype.card V:ℝ))
    (hExtra:(Slocal.card:ℝ)≤β*Fintype.card V/4):
    ∃ (g:X→V) (F:SimpleGraph V),
      let C:=as.toFinset;
      let Es:=prescribedCyclePhysicalEdges as;
      let added:=Es.image (Sym2.map g);
      let st':PrescribedFamilyState I X V:=
        ⟨Function.update st.assigned k (st.assigned k∪C),
         Function.update st.vertexMap k g,st.freeOccurrences∪({k}:Finset I).product C,
         Function.update st.sourceEdges k (st.sourceEdges k∪Es),
         Function.update st.physicalEdges k (st.physicalEdges k∪added),
         Function.update st.newEdges k (st.newEdges k∪added)⟩;
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      (∀v,(((st'.freeOccurrences.filter (fun p=>p.1∈H)).filter
        (fun p=>familyVertexImage st'.vertexMap p=v)).card:ℝ)≤tLocal+1) ∧
      (∀ x∈st.assigned k,g x=st.vertexMap k x) ∧
      DirectedCycleThrough D F (as.map g) ∧
      ∀ x∈as,g x∈L :=by
  let n:ℝ:=Fintype.card V
  let S:Finset V:=Finset.univ.filter (fun v=>(Real.sqrt δ*n:ℝ)≤
    (st.freeOccurrences.filter (fun p=>familyVertexImage st.vertexMap p=v)).card)
  have hdis:Disjoint (st.assigned k) as.toFinset:=by
    apply Finset.disjoint_left.mpr
    intro x hx hxs
    exact hfree x (List.mem_toFinset.mp hxs) hx
  have hsub:st.assigned k∪as.toFinset⊆QV k:=by
    intro x hx
    rcases Finset.mem_union.mp hx with hx|hx
    · exact hvalid.2.2.1 k hx
    · exact hsubset x (List.mem_toFinset.mp hx)
  have hresources:=prescribed_family_state_resources st QV Q A₀ ψ E₀ J β δ n
    hβ hβ1 hδ hδbound hnβ hn hI hQsize hQdegree hold hJ hvalid
  have hS:(S.card:ℝ)≤Real.sqrt δ*n:=hresources.1
  have hM:0≤8*Real.sqrt δ*n:=by
    have hroot:0<Real.sqrt δ:=Real.sqrt_pos.2 hδ
    have hnpos:0<n:=by have :0<2/Real.sqrt δ:=div_pos (by norm_num) hroot;linarith
    positivity
  have hbud:=prescribed_extra_saturation_component_budgets (QV k) (st.assigned k) as has hsub hdis
    (st.vertexMap k) S Slocal (8*Real.sqrt δ*n) β δ n hβ hβ1 hδ hδstrong hnstrong
    (hQsize k) hS hExtra hM le_rfl
  have hroom:=hbud.2.2.1
  exact prescribed_family_free_cycle_restricted_advance st QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound
    hnβ hn hI hQsize hQdegree hold hJ hvalid k as has hlen hfree hsubset Dsrc Fsrc hDQ hsrc
    D L hext H tLocal Slocal hLocal hSat (by simpa only [S,n] using hroom)
end Oberwolfach
