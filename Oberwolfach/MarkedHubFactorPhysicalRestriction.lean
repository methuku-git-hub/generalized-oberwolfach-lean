module

public import Oberwolfach.MarkedHubFactorOn
public import Oberwolfach.MarkedWheelRestriction

@[expose] public section

/-! A selected factor avoiding a physical deletion is the same factor in
the remaining typed host. Neither its vertices nor its cycle coordinates
are changed. Spoke avoidance is checked on the entire specified class. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E K:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:K→V} {m b:ℕ} {π:Equiv.Perm V} {H₀ HK:V→U→Prop}

theorem marked_hub_factor_physical_restriction (hm:1≤m) (hb:1≤b)
    (u:U) (Y:Finset V) (P:MarkedHubFactorOn tail head ktail khead m π b H₀ HK u Y)
    (D:SimpleGraph (V⊕U)) (hPD:Disjoint P.graph D)
    (hsp:∀ v∈Y,¬D.Adj (Sum.inl v) (Sum.inr u)):
    ∃ P':MarkedHubFactorOn
      (fun e:{e:E // ¬D.Adj (Sum.inl (tail e)) (Sum.inl (head e))}=>tail e.val) (fun e=>head e.val)
      (fun e:{e:K // ¬D.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))}=>ktail e.val) (fun e=>khead e.val)
      m π b (fun v u=>H₀ v u∧¬D.Adj (Sum.inl v) (Sum.inr u))
        (fun v u=>HK v u∧¬D.Adj (Sum.inl v) (Sum.inr u)) u Y,
      P'.rim=P.rim∧P'.graph=P.graph :=by
  let PE:=fun e:E=>¬D.Adj (Sum.inl (tail e)) (Sum.inl (head e))
  let PK:=fun e:K=>¬D.Adj (Sum.inl (ktail e)) (Sum.inl (π (khead e)))
  let H₀':=fun v u=>H₀ v u∧¬D.Adj (Sum.inl v) (Sum.inr u)
  let HK':=fun v u=>HK v u∧¬D.Adj (Sum.inl v) (Sum.inr u)
  have hedge (C:P.cycles) (i:Fin (m+1)):
      ¬D.Adj (Sum.inl (C.val.val i)) (Sum.inl (twistedTupleHead π C.val.val i)):=by
    have hpair:=markedCycle_physical_pair tail head ktail khead π b (hubCycleAsMarked u C.val) i
    have hc:=markedCycle_physical_edge_card tail head ktail khead m π b hm hb (hubCycleAsMarked u C.val) i
    rw [hpair] at hc
    change ({C.val.val i,twistedTupleHead π C.val.val i}:Finset V).card=2 at hc
    have hn:C.val.val i≠twistedTupleHead π C.val.val i:=by
      intro he
      simp only [he,Finset.pair_eq_singleton,Finset.card_singleton] at hc
      omega
    have he:P.rim.Adj (C.val.val i) (twistedTupleHead π C.val.val i):=by
      refine ⟨hn,Finset.mem_biUnion.mpr ⟨C.val,C.property,?_⟩⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hpair⟩
    have he':P.graph.Adj (Sum.inl (C.val.val i)) (Sum.inl (twistedTupleHead π C.val.val i)):=by
      rw [MarkedHubFactorOn.graph,SimpleGraph.map_adj']
      exact ⟨fun h=>hn (Sum.inl.inj h),_,_,he,rfl,rfl⟩
    exact disjoint_graphs_no_common_edge _ _ hPD _ _ he'
  have hrow (C:P.cycles) (i:Fin (m+1)):C.val.val i∈Y:=by
    apply P.covers.subset
    exact Finset.mem_biUnion.mpr ⟨C.val,C.property,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  have hvalid (C:P.cycles):
      IsMarkedCycleTuple (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
        (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b C.val.val∧
      MarkedHubCompatible H₀' HK' C.val.val u:=by
    refine ⟨⟨C.val.property.1.1,?_,?_⟩,?_,?_⟩
    · intro j
      obtain ⟨e,ht,hh⟩:=C.val.property.1.2.1 j
      refine ⟨⟨e,?_⟩,ht,hh⟩
      dsimp [PE]
      rw [ht,hh]
      simpa only [twistedTupleHead,Fin.snoc_castSucc] using hedge C j.castSucc
    · obtain ⟨e,ht,hh⟩:=C.val.property.1.2.2
      refine ⟨⟨e,?_⟩,ht,hh⟩
      dsimp [PK]
      rw [ht,hh]
      simpa only [twistedTupleHead,Fin.snoc_last] using hedge C (Fin.last m)
    · exact ⟨C.val.property.2.1,hsp _ (hrow C 0)⟩
    · intro i
      exact ⟨C.val.property.2.2 i,hsp _ (hrow C i.succ)⟩
  let f:=fun C:P.cycles=>(⟨C.val.val,hvalid C⟩:
    HubMarkedCycle (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK' u)
  have hvertices (C:P.cycles):hubMarkedCycleVertices u (f C)=hubMarkedCycleVertices u C.val:=rfl
  have hphysical (C:P.cycles):hubCyclePhysicalEdges u (f C)=hubCyclePhysicalEdges u C.val:=by
    have hh:=markedCycleToLarger_physical PE PK (hubCycleAsMarked u (f C))
    exact hh.symm
  let P':MarkedHubFactorOn (fun e:{e // PE e}=>tail e.val) (fun e=>head e.val)
      (fun e:{e // PK e}=>ktail e.val) (fun e=>khead e.val) m π b H₀' HK' u Y:=
    { cycles:=Finset.univ.image f
      disjoint:=by
        intro C hC Z hZ hne
        obtain ⟨C,_,rfl⟩:=Finset.mem_image.mp hC
        obtain ⟨Z,_,rfl⟩:=Finset.mem_image.mp hZ
        rw [hvertices,hvertices]
        apply P.disjoint C.val C.property Z.val Z.property
        intro he
        exact hne (congrArg f (Subtype.ext he))
      covers:=by
        apply Eq.trans (b:=P.cycles.biUnion (hubMarkedCycleVertices u)) _ P.covers
        ext v
        simp only [Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
        constructor
        · rintro ⟨C,⟨D,rfl⟩,hv⟩
          exact ⟨D.val,D.property,hv⟩
        · rintro ⟨C,hC,hv⟩
          exact ⟨f ⟨C,hC⟩,⟨⟨C,hC⟩,rfl⟩,hv⟩ }
  have hr:P'.rim=P.rim:=by
    unfold MarkedHubFactorOn.rim
    congr 1
    ext e
    simp only [P',Finset.mem_biUnion,Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨C,⟨D,rfl⟩,he⟩
      exact ⟨D.val,D.property,by rwa [hphysical] at he⟩
    · rintro ⟨C,hC,he⟩
      exact ⟨f ⟨C,hC⟩,⟨⟨C,hC⟩,rfl⟩,by rwa [hphysical]⟩
  exact ⟨P',hr,congrArg (fun G:SimpleGraph V=>G.map (Sum.inl:V→V⊕U)) hr⟩

end Oberwolfach
