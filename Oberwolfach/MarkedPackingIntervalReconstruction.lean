module

public import Oberwolfach.MarkedPackingHubRimPartition
public import Oberwolfach.MarkedHubFactorIntervalFamilyVertices

@[expose] public section
/-! Reconstruct all prescribed intervals from a physical marked-wheel packing,
with hubwise vertex partitions and a global physical-rim edge partition. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 40000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_packing_interval_reconstruction
    {V U E K:Type*} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V→U→Prop)
    (P:Finset (MarkedWheel tail head ktail khead m π b H₀ Hₖ))
    (hP:∀W∈P,∀Z∈P,W≠Z→Disjoint (markedWheelPhysicalResources W) (markedWheelPhysicalResources Z))
    (hspoke:∀v u,Sum.inr (v,u)∈P.biUnion markedWheelPhysicalResources ↔ H₀ v u∨Hₖ v u)
    (Y:U→Finset V) (hmarked:∀u x,Hₖ x u↔x∈Y u) (hsep:∀u x,Hₖ x u→¬H₀ x u)
    (J:U→Type*) [∀u,Fintype (J u)] (k:∀u,J u→ℕ) (v:∀u j,Fin (k u j+1)↪V)
    (hroots:∀u j (i:Fin (k u j)),v u j i.castSucc∈Y u)
    (hnext:∀u j (i:Fin (k u j)),π (v u j i.castSucc)=v u j i.succ)
    (hend:∀u j,v u j (Fin.last (k u j))∉Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u))
    (hrootdis:∀u (j l:J u),j≠l→∀i:Fin (k u j),∀t:Fin (k u l),v u j i.castSucc≠v u l t.castSucc)
    (hYcover:∀u x,x∈Y u→∃j:J u,∃i:Fin (k u j),v u j i.castSucc=x)
    (hendDistinct:∀u (j l:J u),j≠l→v u j (Fin.last (k u j))≠v u l (Fin.last (k u l)))
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∃M:∀u:U,Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u),
    ∃q:∀u (j:J u),G.Walk (v u j 0) (v u j (Fin.last (k u j))),
      (∀u j,(q u j).IsPath ∧ (q u j).length=k u j*(m+1)) ∧
      (∀u (j l:J u),j≠l→Disjoint (q u j).support.toFinset (q u l).support.toFinset) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>(q u j).support.toFinset))=
        (Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) ∪
          Finset.univ.image (fun j:J u=>v u j (Fin.last (k u j)))) ∧
      (∀u (j l:J u),j≠l→Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q u l))) ∧
      (∀u w:U,u≠w→∀j:J u,∀l:J w,Disjoint (walkPhysicalEdges (q u j)) (walkPhysicalEdges (q w l))) ∧
      (∀u,(Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=(M u).biUnion (hubCyclePhysicalEdges u)) ∧
      Finset.univ.biUnion (fun u:U=>Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=
        P.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1) := by
  obtain ⟨M,hM,hcross,hglobal⟩:=marked_packing_hub_rim_partition P hP hspoke
  have hYS:∀u,Y u⊆Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u):=by
    intro u x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact Or.inr ((hmarked u x).2 hx)
  have hexist:∀u:U,∃q:∀j:J u,G.Walk (v u j 0) (v u j (Fin.last (k u j))),
      (∀j,(q j).IsPath ∧ (q j).length=k u j*(m+1)) ∧
      (∀j l:J u,j≠l→Disjoint (q j).support.toFinset (q l).support.toFinset) ∧
      (Finset.univ.biUnion (fun j:J u=>(q j).support.toFinset))=
        (Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) ∪ Finset.univ.image (fun j:J u=>v u j (Fin.last (k u j))) ∧
      (∀j l:J u,j≠l→Disjoint (walkPhysicalEdges (q j)) (walkPhysicalEdges (q l))) ∧
      (Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q j)))=(M u).biUnion (hubCyclePhysicalEdges u):=by
    intro u
    obtain ⟨select,hselected,q,hq,hedgepair,hedgecover,hvertexpair,hvertexcover⟩:=
      marked_hub_factor_interval_family_with_vertices G tail head ktail khead m b π hb H₀ Hₖ u (M u)
        (hM u).1 (Finset.univ.filter (fun x=>H₀ x u∨Hₖ x u)) (Y u) (hM u).2.1 (hYS u)
        (hmarked u) (hsep u) (k u) (v u) (hroots u) (hnext u) (hend u) (hrootdis u) (hYcover u)
        (hendDistinct u) hE hK hphysical
    exact ⟨q,(fun j=>⟨(hq j).1,(hq j).2.1⟩),hvertexpair,hvertexcover,hedgepair,hedgecover⟩
  let q:∀u (j:J u),G.Walk (v u j 0) (v u j (Fin.last (k u j))):=fun u=>Classical.choose (hexist u)
  have hq:=fun u=>Classical.choose_spec (hexist u)
  have hsub:∀u (j:J u),walkPhysicalEdges (q u j)⊆(M u).biUnion (hubCyclePhysicalEdges u):=by
    intro u j e he
    rw [←(hq u).2.2.2.2] 
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,he⟩
  refine ⟨M,q,?_,?_,?_,?_,?_,?_,?_⟩
  · intro u j;exact (hq u).1 j
  · intro u;exact (hq u).2.1
  · intro u;exact (hq u).2.2.1
  · intro u;exact (hq u).2.2.2.1
  · intro u w huw j l
    exact (hcross u w huw).mono (hsub u j) (hsub w l)
  · intro u;exact (hq u).2.2.2.2
  · calc
      Finset.univ.biUnion (fun u:U=>Finset.univ.biUnion (fun j:J u=>walkPhysicalEdges (q u j)))=
          Finset.univ.biUnion (fun u:U=>(M u).biUnion (hubCyclePhysicalEdges u)):=by
            apply Finset.biUnion_congr rfl
            intro u hu
            exact (hq u).2.2.2.2
      _=P.biUnion (fun W=>markedCyclePhysicalEdges tail head ktail khead m π b W.1):=hglobal
end Oberwolfach
