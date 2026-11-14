module

public import Oberwolfach.MarkedHubIntervalFixedSelectionDirected
public import Oberwolfach.MarkedHubFactorRootBijection
public import Oberwolfach.FiniteBiUnionPartition

@[expose] public section
/-! Reconstruct all successor intervals at one marked hub with exact,
pairwise disjoint physical-edge coverage of its hub factor. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 30000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem marked_hub_factor_interval_family_directed
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
      (∀j,walkPhysicalArcs (q j)=Finset.univ.biUnion (fun i:Fin (k j)=>
        markedCyclePhysicalArcs tail head ktail khead m π b
          ⟨(select ⟨v j i.castSucc,hroots j i⟩).val,(select ⟨v j i.castSucc,hroots j i⟩).property.1⟩)) ∧
      Finset.univ.biUnion (fun j=>walkPhysicalArcs (q j))=M.biUnion (fun C=>
        markedCyclePhysicalArcs tail head ktail khead m π b (hubCycleAsMarked u C)) := by
  obtain ⟨select,hselected,honto⟩:=marked_hub_factor_root_bijection tail head ktail khead m b π H₀ Hₖ u M hM S Y hcover hYS hmarked hsep
  have hexist:∀j:J,∃q:G.Walk (v j 0) (v j (Fin.last (k j))),q.IsPath ∧ q.length=k j*(m+1) ∧
        (∀x,x∈q.support ↔ x=v j (Fin.last (k j)) ∨
          ∃i:Fin (k j),∃a:Fin (m+1),(select ⟨v j i.castSucc,hroots j i⟩).val a=x) ∧
        walkPhysicalEdges q=Finset.univ.biUnion (fun i:Fin (k j)=>
          markedCyclePhysicalEdges tail head ktail khead m π b
            ⟨(select ⟨v j i.castSucc,hroots j i⟩).val,(select ⟨v j i.castSucc,hroots j i⟩).property.1⟩) ∧
        walkPhysicalArcs q=Finset.univ.biUnion (fun i:Fin (k j)=>
          markedCyclePhysicalArcs tail head ktail khead m π b
            ⟨(select ⟨v j i.castSucc,hroots j i⟩).val,(select ⟨v j i.castSucc,hroots j i⟩).property.1⟩):=by
    intro j
    exact marked_hub_factor_interval_path_for_selection_directed G tail head ktail khead m b π hb H₀ Hₖ u M hM S Y hcover hYS
      (fun x hx=>(hmarked x).2 hx) hsep select hselected (v j) (hroots j) (hnext j) (hend j) hE hK
  let q:∀j:J,G.Walk (v j 0) (v j (Fin.last (k j))):=fun j=>Classical.choose (hexist j)
  have hq:∀j,(q j).IsPath ∧ (q j).length=k j*(m+1) ∧
        (∀x,x∈(q j).support ↔ x=v j (Fin.last (k j)) ∨
          ∃i:Fin (k j),∃a:Fin (m+1),(select ⟨v j i.castSucc,hroots j i⟩).val a=x) ∧
        walkPhysicalEdges (q j)=Finset.univ.biUnion (fun i:Fin (k j)=>
          markedCyclePhysicalEdges tail head ktail khead m π b
            ⟨(select ⟨v j i.castSucc,hroots j i⟩).val,(select ⟨v j i.castSucc,hroots j i⟩).property.1⟩):=
    fun j=>⟨(Classical.choose_spec (hexist j)).1,(Classical.choose_spec (hexist j)).2.1,
      (Classical.choose_spec (hexist j)).2.2.1,(Classical.choose_spec (hexist j)).2.2.2.1⟩
  have hqarc:∀j,walkPhysicalArcs (q j)=Finset.univ.biUnion (fun i:Fin (k j)=>
      markedCyclePhysicalArcs tail head ktail khead m π b
        ⟨(select ⟨v j i.castSucc,hroots j i⟩).val,(select ⟨v j i.castSucc,hroots j i⟩).property.1⟩):=
    fun j=>(Classical.choose_spec (hexist j)).2.2.2.2
  let blocks:J→Finset {x // x∈Y}:=fun j=>Finset.univ.image (fun i:Fin (k j)=>⟨v j i.castSucc,hroots j i⟩)
  let g:{x // x∈Y}→Finset (Finset V):=fun x=>hubCyclePhysicalEdges u (select x)
  have hblocks:∀j l:J,j≠l→Disjoint (blocks j) (blocks l):=by
    intro j l hjl
    apply Finset.disjoint_left.mpr
    intro x hxj hxl
    obtain ⟨i,_,hi⟩:=Finset.mem_image.mp hxj
    obtain ⟨t,_,ht⟩:=Finset.mem_image.mp hxl
    have heq:v j i.castSucc=v l t.castSucc:=
      (congrArg Subtype.val hi).trans (congrArg Subtype.val ht).symm
    exact hrootdis j l hjl i t heq
  have hbc:Finset.univ.biUnion blocks=Finset.univ:=by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and,iff_true]
    obtain ⟨j,i,hi⟩:=hYcover x.val x.property
    refine ⟨j,?_⟩
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,Subtype.ext hi⟩
  have hgedges:∀x y:{x // x∈Y},x≠y→Disjoint (g x) (g y):=by
    intro x y hxy
    have hne:select x≠select y:=fun h=>hxy (select.injective h)
    exact marked_factor_physical_edges_disjoint u hphysical M hM (select x) (hselected x).1 (select y) (hselected y).1 hne
  have hpair:∀j l:J,j≠l→Disjoint ((blocks j).biUnion g) ((blocks l).biUnion g):=by
    intro j l hjl
    apply Finset.disjoint_left.mpr
    intro x hxj hxl
    obtain ⟨r,hrj,hxr⟩:=Finset.mem_biUnion.mp hxj
    obtain ⟨s,hsl,hxs⟩:=Finset.mem_biUnion.mp hxl
    have hrs:r≠s:=by
      intro h
      subst s
      exact Finset.disjoint_left.mp (hblocks j l hjl) hrj hsl
    exact Finset.disjoint_left.mp (hgedges r s hrs) hxr hxs
  have hunion:Finset.univ.biUnion (fun j=>(blocks j).biUnion g)=Finset.univ.biUnion g:=by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,r,hr,hx⟩
      exact ⟨r,hx⟩
    · rintro ⟨r,hx⟩
      have hr:r∈Finset.univ.biUnion blocks:=by rw [hbc];exact Finset.mem_univ r
      obtain ⟨j,_,hrj⟩:=Finset.mem_biUnion.mp hr
      exact ⟨j,r,hrj,hx⟩
  have hqblock:∀j,walkPhysicalEdges (q j)=(blocks j).biUnion g:=by
    intro j
    rw [(hq j).2.2.2]
    simp [blocks,g,Finset.image_biUnion,hubCyclePhysicalEdges,hubCycleAsMarked]
  have hall:Finset.univ.biUnion g=M.biUnion (hubCyclePhysicalEdges u):=by
    ext e
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,hx⟩
      exact ⟨select x,(hselected x).1,hx⟩
    · rintro ⟨C,hCM,hC⟩
      obtain ⟨x,hx⟩:=honto C hCM
      exact ⟨x,by simpa [g,hx] using hC⟩
  let ga:{x // x∈Y}→Finset (V×V):=fun x=>
    markedCyclePhysicalArcs tail head ktail khead m π b (hubCycleAsMarked u (select x))
  have hqblockA:∀j,walkPhysicalArcs (q j)=(blocks j).biUnion ga:=by
    intro j
    rw [hqarc j]
    simp [blocks,ga,Finset.image_biUnion,hubCycleAsMarked]
  have hunionA:Finset.univ.biUnion (fun j=>(blocks j).biUnion ga)=Finset.univ.biUnion ga:=by
    ext x
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,r,hr,hx⟩;exact ⟨r,hx⟩
    · rintro ⟨r,hx⟩
      have hr:r∈Finset.univ.biUnion blocks:=by rw [hbc];exact Finset.mem_univ r
      obtain ⟨j,_,hrj⟩:=Finset.mem_biUnion.mp hr
      exact ⟨j,r,hrj,hx⟩
  have hallA:Finset.univ.biUnion ga=M.biUnion (fun C=>
      markedCyclePhysicalArcs tail head ktail khead m π b (hubCycleAsMarked u C)):=by
    ext e
    simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨x,hx⟩;exact ⟨select x,(hselected x).1,hx⟩
    · rintro ⟨C,hCM,hC⟩
      obtain ⟨x,hx⟩:=honto C hCM
      exact ⟨x,by simpa [ga,hx] using hC⟩
  refine ⟨select,hselected,q,hq,?_,?_,hqarc,?_⟩
  · intro j l hjl
    rw [hqblock j,hqblock l]
    exact hpair j l hjl
  · simp_rw [hqblock]
    exact hunion.trans hall
  · simp_rw [hqblockA]
    exact hunionA.trans hallA
end Oberwolfach
