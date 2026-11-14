module

public import Oberwolfach.PrescribedFamilyPhysicalDegree
public import Oberwolfach.PartialImageDegree
public import Oberwolfach.BoundedImageUnionDegrees

@[expose] public section
/-! The physical union of degree-two source graphs has degree at most twice
the number of actual factor images containing the vertex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem prescribed_physical_union_degree_from_image_load
    {I V:Type} [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
    (X:I→Type) [∀i,Fintype (X i)] [∀i,DecidableEq (X i)]
    (Q:∀i,SimpleGraph (X i)) (Φ:∀i,X i→V)
    (hinj:∀i,Function.Injective (Φ i)) (hdeg:∀i x,(Q i).degree x≤2)
    (v:V) (L:ℝ)
    (hload:((Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))).card:ℝ)≤L):
    let E:I→Finset (Sym2 V):=fun i=>(Q i).edgeFinset.image (Sym2.map (Φ i));
    ((prescribedPhysicalUnion E).degree v:ℝ)≤2*L :=by
  intro E
  let f:∀i,X i↪V:=fun i=>⟨Φ i,hinj i⟩
  let G:I→SimpleGraph V:=fun i=>(Q i).map (f i)
  have hsource:∀i x,(G i).degree x≤(if ∃y,Φ i y=x then 2 else 0):=by
    intro i x
    convert partial_injective_image_degree (Q i) (f i) (G i) (le_refl _) (hdeg i) x using 1 <;>
      congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  have hcover:(prescribedPhysicalUnion E).neighborFinset v⊆Finset.univ.biUnion (fun i=>(G i).neighborFinset v):=by
    intro x hx
    have hAdj:(prescribedPhysicalUnion E).Adj v x:=by simpa only [SimpleGraph.mem_neighborFinset] using hx
    have he:s(v,x)∈Finset.univ.biUnion E:=by
      have hh:=((SimpleGraph.fromEdgeSet_adj _).mp hAdj).1
      exact hh
    obtain ⟨i,_,hi⟩:=Finset.mem_biUnion.mp he
    have hi':s(v,x)∈(G i).edgeFinset:=by
      have hmap:(fun e:Sym2 (X i)=>(f i).sym2Map e)=Sym2.map (Φ i):=by
        funext e
        induction e using Sym2.ind with
        | _ a b => rfl
      simpa only [E,G,SimpleGraph.edgeFinset_map,Finset.map_eq_image,hmap] using hi
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    simpa only [SimpleGraph.mem_neighborFinset,SimpleGraph.mem_edgeSet] using (SimpleGraph.mem_edgeFinset.mp hi')
  have hnat:(prescribedPhysicalUnion E).degree v≤2*(Finset.univ.filter (fun i=>∃y,Φ i y=v)).card:=by
    rw [←SimpleGraph.card_neighborFinset_eq_degree]
    have hh:=degree_two_image_union_bound G (fun i x=>∃y,Φ i y=x)
      (by intro i x; convert hsource i x using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) v
    have hc:=Finset.card_le_card hcover
    convert hc.trans (by convert hh using 1 <;> congr! 10 <;> first | rfl | exact Subsingleton.elim _ _) using 1 <;>
      congr! 10 <;> first | rfl | exact Subsingleton.elim _ _
  have hreal:((prescribedPhysicalUnion E).degree v:ℝ)≤2*((Finset.univ.filter (fun i=>∃y,Φ i y=v)).card:ℝ):=by exact_mod_cast hnat
  have heq:(Finset.univ.filter (fun i=>∃y,Φ i y=v))=(Finset.univ.filter (fun i=>v∈Finset.univ.image (Φ i))):=by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  rw [heq] at hreal
  linarith
end Oberwolfach
