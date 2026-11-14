module

public import Oberwolfach.MarkedHubFactorIntervalFamily
public import Oberwolfach.MarkedHubFactorSelectionOnto

@[expose] public section
/-! Reconstruct all successor intervals at one marked hub with exact,
pairwise disjoint physical-edge coverage of its hub factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_interval_family_with_vertices
    {V U E K J:Type*} [Fintype V] [instV:DecidableEq V] [Fintype J]
    (G:SimpleGraph V) (tail head:E→V) (ktail khead:K→V)
    (m b:ℕ) (π:Equiv.Perm V) (hb:1≤b) (H₀ Hₖ:V→U→Prop) (u:U)
    (M:Finset (HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u))
    (hM:∀C∈M,∀D∈M,C≠D→Disjoint (hubMarkedCycleVertices u C) (hubMarkedCycleVertices u D))
    (S Y:Finset V) (hcover:M.biUnion (hubMarkedCycleVertices u)=S)
    (hYS:Y⊆S) (hmarked:∀x,Hₖ x u↔x∈Y) (hsep:∀x,Hₖ x u→¬H₀ x u)
    (k:J→ℕ) (v:∀j:J,Fin (k j+1)↪V)
    (hroots:∀j (i:Fin (k j)),v j i.castSucc∈Y)
    (hnext:∀j (i:Fin (k j)),π (v j i.castSucc)=v j i.succ)
    (hend:∀j,v j (Fin.last (k j))∉S)
    (hrootdis:∀j l:J,j≠l→∀i:Fin (k j),∀t:Fin (k l),v j i.castSucc≠v l t.castSucc)
    (hYcover:∀x∈Y,∃j:J,∃i:Fin (k j),v j i.castSucc=x)
    (hendDistinct:∀j l:J,j≠l→v j (Fin.last (k j))≠v l (Fin.last (k l)))
    (hE:∀e:E,G.Adj (tail e) (head e)) (hK:∀e:K,G.Adj (ktail e) (π (khead e)))
    (hphysical:Function.Injective (markedPhysicalEdge tail head ktail khead π)):
    ∃select:{x // x∈Y}↪HubMarkedCycle tail head ktail khead m π b H₀ Hₖ u,
      (∀x,select x∈M ∧ (select x).val 0=x.val) ∧
    ∃q:∀j:J,G.Walk (v j 0) (v j (Fin.last (k j))),
      (∀j,(q j).IsPath ∧ (q j).length=k j*(m+1) ∧
        (∀x,x∈(q j).support ↔ x=v j (Fin.last (k j)) ∨
          ∃i:Fin (k j),∃a:Fin (m+1),(select ⟨v j i.castSucc,hroots j i⟩).val a=x) ∧
        walkPhysicalEdges (q j)=Finset.univ.biUnion (fun i:Fin (k j)=>
          markedCyclePhysicalEdges tail head ktail khead m π b
            ⟨(select ⟨v j i.castSucc,hroots j i⟩).val,(select ⟨v j i.castSucc,hroots j i⟩).property.1⟩)) ∧
      (∀j l:J,j≠l→Disjoint (walkPhysicalEdges (q j)) (walkPhysicalEdges (q l))) ∧
      Finset.univ.biUnion (fun j=>walkPhysicalEdges (q j))=M.biUnion (hubCyclePhysicalEdges u) ∧
      (∀j l:J,j≠l→Disjoint (q j).support.toFinset (q l).support.toFinset) ∧
      Finset.univ.biUnion (fun j=>(q j).support.toFinset)=
        S ∪ Finset.univ.image (fun j=>v j (Fin.last (k j))) := by
  obtain ⟨select,hselected,q,hq,hedgepair,hedgecover⟩:=marked_hub_factor_interval_family G tail head ktail khead m b π hb H₀ Hₖ u M hM S Y hcover hYS hmarked hsep k v hroots hnext hend hrootdis hYcover hE hK hphysical
  have honto:=marked_hub_factor_selection_onto tail head ktail khead m b π H₀ Hₖ u M hM Y hmarked select hselected
  have hinnerS:∀j (i:Fin (k j)) (a:Fin (m+1)),(select ⟨v j i.castSucc,hroots j i⟩).val a∈S:=by
    intro j i a
    rw [←hcover]
    refine Finset.mem_biUnion.mpr ⟨select ⟨v j i.castSucc,hroots j i⟩,(hselected _).1,?_⟩
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  have hsepVertices:∀j l:J,j≠l→∀i:Fin (k j),∀t:Fin (k l),∀a b:Fin (m+1),
      (select ⟨v j i.castSucc,hroots j i⟩).val a≠(select ⟨v l t.castSucc,hroots l t⟩).val b:=by
    intro j l hjl i t a b heq
    let x:{x // x∈Y}:=⟨v j i.castSucc,hroots j i⟩
    let y:{x // x∈Y}:=⟨v l t.castSucc,hroots l t⟩
    have hxy:x≠y:=by
      intro he
      exact hrootdis j l hjl i t (congrArg Subtype.val he)
    have hne:select x≠select y:=fun he=>hxy (select.injective he)
    have hd:=hM (select x) (hselected x).1 (select y) (hselected y).1 hne
    apply Finset.disjoint_left.mp hd
      (show (select x).val a∈hubMarkedCycleVertices u (select x) from Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)
    rw [heq]
    exact Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩
  refine ⟨select,hselected,q,hq,hedgepair,hedgecover,?_,?_⟩
  · intro j l hjl
    apply Finset.disjoint_left.mpr
    intro x hxj hxl
    have hj: x∈(q j).support:=List.mem_toFinset.mp hxj
    have hl: x∈(q l).support:=List.mem_toFinset.mp hxl
    rcases ((hq j).2.2.1 x).mp hj with hjend | ⟨i,a,ha⟩
    · rcases ((hq l).2.2.1 x).mp hl with hlend | ⟨t,b,hb⟩
      · exact hendDistinct j l hjl (hjend.symm.trans hlend)
      · apply hend j
        rw [←hjend,←hb]
        exact hinnerS l t b
    · rcases ((hq l).2.2.1 x).mp hl with hlend | ⟨t,b,hb⟩
      · apply hend l
        rw [←hlend,←ha]
        exact hinnerS j i a
      · exact hsepVertices j l hjl i t a b (ha.trans hb.symm)
  · ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,List.mem_toFinset,Finset.mem_union,Finset.mem_image]
    constructor
    · rintro ⟨j,hx⟩
      rcases ((hq j).2.2.1 x).mp hx with hjend | ⟨i,a,ha⟩
      · right;exact ⟨j,hjend.symm⟩
      · left;rw [←ha];exact hinnerS j i a
    · rintro (hx|⟨j,hjend⟩)
      · rw [←hcover] at hx
        obtain ⟨C,hCM,hxC⟩:=Finset.mem_biUnion.mp hx
        obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hxC
        obtain ⟨y,hy⟩:=honto C hCM
        obtain ⟨j,i,hi⟩:=hYcover y.val y.property
        have heq:(⟨v j i.castSucc,hroots j i⟩:{x // x∈Y})=y:=Subtype.ext hi
        have hc:select ⟨v j i.castSucc,hroots j i⟩=C:=by rw [heq];exact hy
        refine ⟨j,((hq j).2.2.1 x).mpr (Or.inr ⟨i,a,?_⟩)⟩
        rw [hc]
        exact ha
      · refine ⟨j,((hq j).2.2.1 x).mpr (Or.inl ?_)⟩
        exact hjend.symm
end Oberwolfach
