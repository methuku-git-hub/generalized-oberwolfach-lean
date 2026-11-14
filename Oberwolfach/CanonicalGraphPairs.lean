module

public import Oberwolfach.OrdinaryWheelResources
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! One fixed ordered representative of each undirected edge, shared by
all cycle identifiers. Disjointness of these pair sets therefore means
physical edge disjointness, independently of cycle orientations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

def canonicalGraphPairs (G:SimpleGraph V):Finset (V×V):=G.edgeFinset.image (fun e=>e.out)

theorem sym2_out_injective : Function.Injective (fun e:Sym2 V=>e.out):=by
  intro e f h
  change e.out=f.out at h
  calc
    e = s(e.out.1,e.out.2):=by rw [Sym2.mk];exact e.out_eq.symm
    _ = s(f.out.1,f.out.2):=by rw [h]
    _ = f:=by rw [Sym2.mk];exact f.out_eq

theorem canonicalGraphPairs_card (G:SimpleGraph V):
    (canonicalGraphPairs G).card=G.edgeFinset.card:=Finset.card_image_of_injective _ sym2_out_injective

theorem canonicalGraphPairs_adj (G:SimpleGraph V) (p:V×V) (hp:p∈canonicalGraphPairs G):G.Adj p.1 p.2:=by
  obtain ⟨e,he,rfl⟩:=Finset.mem_image.mp hp
  have hout:s(e.out.1,e.out.2)=e:=by rw [Sym2.mk];exact e.out_eq
  exact SimpleGraph.mem_edgeFinset.mp (hout.symm ▸ he)

theorem canonicalGraphPairs_incidence (G:SimpleGraph V) (v:V):
    ((canonicalGraphPairs G).filter (fun p=>v=p.1∨v=p.2)).card=G.degree v:=by
  rw [canonicalGraphPairs,Finset.filter_image,Finset.card_image_of_injective _ sym2_out_injective]
  have he:G.edgeFinset.filter (fun e=>v=e.out.1∨v=e.out.2)=G.incidenceFinset v:=by
    rw [G.incidenceFinset_eq_filter]
    apply Finset.filter_congr
    intro e _
    have hout:s(e.out.1,e.out.2)=e:=by rw [Sym2.mk];exact e.out_eq
    calc
      (v=e.out.1∨v=e.out.2) ↔ v∈s(e.out.1,e.out.2):=Sym2.mem_iff.symm
      _ ↔ v∈e:=by rw [hout]
  rw [he,G.card_incidenceFinset_eq_degree]

theorem canonicalGraphPairs_disjoint_iff (G H:SimpleGraph V):
    Disjoint (canonicalGraphPairs G) (canonicalGraphPairs H)↔Disjoint G H:=by
  constructor
  · intro hd
    apply disjoint_iff_inf_le.mpr
    intro a b hab
    exact (Finset.disjoint_left.mp hd
      (Finset.mem_image.mpr ⟨s(a,b),SimpleGraph.mem_edgeFinset.mpr hab.1,rfl⟩)
      (Finset.mem_image.mpr ⟨s(a,b),SimpleGraph.mem_edgeFinset.mpr hab.2,rfl⟩)).elim
  · intro hd
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact disjoint_iff_inf_le.mp hd ⟨canonicalGraphPairs_adj G p hp,canonicalGraphPairs_adj H p hq⟩

theorem canonicalGraphPairs_iSup {I:Type} [Fintype I] [DecidableEq I]
    (G:I→SimpleGraph V):canonicalGraphPairs (⨆ i,G i)=Finset.univ.biUnion (fun i=>canonicalGraphPairs (G i)):=by
  ext p
  simp only [canonicalGraphPairs,Finset.mem_image,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨e,he,rfl⟩
    induction e using Sym2.ind with
    | _ a b=>
      obtain ⟨i,hi⟩:=SimpleGraph.iSup_adj.mp (SimpleGraph.mem_edgeFinset.mp he)
      exact ⟨i,s(a,b),SimpleGraph.mem_edgeFinset.mpr hi,rfl⟩
  · rintro ⟨i,e,he,rfl⟩
    refine ⟨e,?_,rfl⟩
    induction e using Sym2.ind with
    | _ a b=>exact SimpleGraph.mem_edgeFinset.mpr (SimpleGraph.iSup_adj.mpr ⟨i,SimpleGraph.mem_edgeFinset.mp he⟩)

end Oberwolfach
