module

public import Oberwolfach.PrescribedCycleRootedAdvance
public import Oberwolfach.PrescribedCycleFreeAdvance
public import Oberwolfach.PrescribedCycleRotate

@[expose] public section
/-! Process an arbitrarily presented source cycle, rotating to a prescribed
vertex when one exists. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {I X V:Type} [Fintype I] [Fintype X] [Fintype V] [DecidableEq I] [DecidableEq X] [DecidableEq V]

theorem prescribed_cycle_family_advance
    (QV:I→Finset X) (Q:I→SimpleGraph X) (A₀:I→Finset X) (ψ:I→X→V)
    (E₀:I→Finset (Sym2 V)) (J:SimpleGraph V)
    (β δ:ℝ) (hβ:0<β) (hβ1:β≤1) (hδ:0<δ) (hδbound:δ≤(β/100)^2)
    (hnβ:100/β≤(Fintype.card V:ℝ)) (hn:2/Real.sqrt δ≤(Fintype.card V:ℝ))
    (hI:(Fintype.card I:ℝ)≤Fintype.card V)
    (hQsize:∀ i,((QV i).card:ℝ)≤δ*Fintype.card V) (hQdegree:∀ i x,(Q i).degree x≤2)
    (hold:∀ v,((Finset.univ.filter (fun i=>∃ x,x∈A₀ i ∧ ψ i x=v)).card:ℝ)≤δ*Fintype.card V)
    (hJ:∀ v,(J.degree v:ℝ)≤δ*Fintype.card V)
    (k:I) (Dsrc:X→X→Prop) (Fsrc:SimpleGraph X) (hDQ:∀ x y,Dsrc x y→(Q k).Adj x y)
    (D:V→V→Prop) (L:Finset V) (hext:IsExtendingList D L β)
    (a:X) (xs:List X) (hnodup:(a::xs).Nodup) (hlen:3≤(a::xs).length)
    (hsourcecycle:DirectedCycleThrough Dsrc Fsrc (a::xs))
    (st:PrescribedFamilyState I X V)
    (hvalid:st.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V))
    (hinit:prescribedInducedSourceEdges (Q k) (A₀ k)⊆st.sourceEdges k)
    (hfree:∀ x∈a::xs,x∉A₀ k→x∉st.assigned k) (hsubset:∀ x∈a::xs,x∈QV k):
    ∃ st':PrescribedFamilyState I X V,
      st'.Valid QV Q A₀ ψ E₀ J (Real.sqrt δ*Fintype.card V) ∧
      st'.assigned=Function.update st.assigned k (st.assigned k∪(a::xs).toFinset) ∧
      (∀ i,st.assigned i⊆st'.assigned i) ∧ (∀ i,st.sourceEdges i⊆st'.sourceEdges i) ∧
      (∀ i x,x∈st.assigned i→st'.vertexMap i x=st.vertexMap i x) ∧
      (∀ x∈a::xs,x∉A₀ k→st'.vertexMap k x∈L) ∧
      (∀ e∈prescribedDirectedPathEdges ((a::xs)++[a]),
        (e.1∈A₀ k ∧ e.2∈A₀ k) ∨ D (st'.vertexMap k e.1) (st'.vertexMap k e.2)) ∧
      (a::xs).toFinset⊆st'.assigned k ∧
      prescribedOrderedPathEdges ((a::xs)++[a])⊆st'.sourceEdges k := by
  by_cases hex:∃ z∈a::xs,z∈A₀ k
  · obtain ⟨z,hzin,hza⟩:=hex
    by_cases ha:a∈A₀ k
    · exact prescribed_cycle_rooted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
        hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext a xs hnodup hlen ha hsourcecycle st hvalid hinit hfree hsubset
    · have hzxs:z∈xs:=by
        rcases List.mem_cons.mp hzin with hz|hz
        · subst z;exact (ha hza).elim
        · exact hz
      obtain ⟨ys,hrotNodup,hrotLen,hrotSet,hrotChain,hrotPhys,hrotDir⟩:=
        prescribed_cycle_rotate a z xs hnodup hzxs (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y)
      have hmem:∀ x,x∈z::ys ↔ x∈a::xs:=by
        intro x
        have hh:=Finset.ext_iff.mp hrotSet x
        simpa only [List.mem_toFinset] using hh.symm
      have hlen':3≤(z::ys).length:=by rw [←hrotLen];exact hlen
      have hc:List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) ((a::xs)++[a]):=
        (prescribed_path_through_chain Dsrc Fsrc xs a a).mp hsourcecycle
      have hc':List.IsChain (fun x y=>Dsrc x y ∧ ¬Fsrc.Adj x y) ((z::ys)++[z]):=hrotChain.mp hc
      have hsource':DirectedCycleThrough Dsrc Fsrc (z::ys):=
        (prescribed_path_through_chain Dsrc Fsrc ys z z).mpr hc'
      have hf:∀ x∈z::ys,x∉A₀ k→x∉st.assigned k:=by intro x hx;exact hfree x ((hmem x).mp hx)
      have hs:∀ x∈z::ys,x∈QV k:=by intro x hx;exact hsubset x ((hmem x).mp hx)
      obtain ⟨last,hl,hExact,hA,hE,hpres,hL,harcs,hvertices,hedges⟩:=
        prescribed_cycle_rooted_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
          hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext z ys hrotNodup hlen' hza hsource' st hvalid hinit hf hs
      refine ⟨last,hl,?_,hA,hE,hpres,?_,?_,?_,?_⟩
      · simpa only [←hrotSet] using hExact
      · intro x hx hnot;exact hL x ((hmem x).mpr hx) hnot
      · intro e he;apply harcs e;rw [←hrotDir];exact he
      · rw [hrotSet];exact hvertices
      · rw [hrotPhys];exact hedges
  · have hnoA:∀ x∈a::xs,x∉A₀ k:=by intro x hx hxa;exact hex ⟨x,hx,hxa⟩
    obtain ⟨last,hl,hExact,hA,hE,hpres,hL,harcs,hvertices,hedges⟩:=
      prescribed_cycle_free_advance QV Q A₀ ψ E₀ J β δ hβ hβ1 hδ hδbound hnβ hn hI
        hQsize hQdegree hold hJ k Dsrc Fsrc hDQ D L hext a xs hnodup hlen hnoA hsourcecycle st hvalid hinit hfree hsubset
    refine ⟨last,hl,hExact,hA,hE,hpres,hL,?_,hvertices,hedges⟩
    intro e he;exact Or.inr (harcs e he)
end Oberwolfach
