module

public import Oberwolfach.MarkedPrescribedRimGeometry
public import Oberwolfach.MarkedFamilyHubLoads

@[expose] public section

/-! Greedy marked wheel packing for prescribed rim arcs. Each new wheel
uses just its prescribed auxiliary arc within the protected row set, and
its hub lies outside J. Free row and hub uses have explicit uniform caps. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 24000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop} {π:Equiv.Perm V} {b l:ℕ} {c ch:ℝ}

theorem marked_prescribed_rim_wheel_packing
    (Q:MarkedHostExtensionCounts tail head ktail khead H₀ HK π b l c ch)
    (hl:2≤l) (hb:1≤b) (hphys:Function.Injective (markedPhysicalEdge tail head ktail khead π))
    (X:Finset V) (J:Finset U) (N K D₀:ℕ) (hK:0<K)
    (x y:Fin N→V) (t:Fin N→Bool) (hx:∀ i,x i∉X) (hy:∀ i,y i∉X)
    (hsep:∀ i,¬PermutationClose π b (x i) (y i))
    (hroot:∀ i,markedArcPresent tail head ktail khead (t i) (x i) (y i))
    (hedge:Function.Injective (fun i=>if t i then ({x i,π (y i)}:Finset V) else {x i,y i}))
    (hend:∀ a,(Finset.univ.filter (fun i=>a=x i∨a=y i)).card≤D₀)
    (hbudget:((Xᶜ).card:ℝ)+(N*(l+5):ℕ)/(K:ℝ)+(l+6)*(2*b+1)+8*(K+D₀:ℕ)<c)
    (hhbudget:(J.card:ℝ)+N/(K:ℝ)+(l+5)*(K+D₀:ℕ)<ch):
    ∃ C:Fin N→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ i,(C i).2.val∉J∧
        Sum.inl (if t i then ({x i,π (y i)}:Finset V) else {x i,y i})∈markedWheelPhysicalResources (C i)∧
        (∀ a∈markedWheelRows (C i),a=x i∨a=y i∨a∈X)∧
        ∀ a,(C i).1.val a∉X→(C i).1.val (finRotate (l+5) a)∉X→
          markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead (l+4) π b (C i).1 a)=
            (if t i then {x i,π (y i)} else {x i,y i}))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))∧
      (∀ a∈X,markedFamilyRowLoad C a≤K)∧(∀ u,markedFamilyHubLoad C u≤K)∧
      (∀ a,(markedFamilyRim C).degree a≤4*(K+D₀))∧
      (∀ a,(Finset.univ.filter (markedFamilySpokes C a)).card≤K+D₀)∧
      (∀ u,(Finset.univ.filter (fun a=>markedFamilySpokes C a u)).card≤K*(l+5)):=by
  let old (i:Fin N):Finset V:=if t i then {x i,π (y i)} else {x i,y i}
  let Good (i:Fin N) (C:MarkedWheel tail head ktail khead (l+4) π b H₀ HK):=
    C.2.val∉J∧Sum.inl (old i)∈markedWheelPhysicalResources C∧
      (∀ a∈markedWheelRows C,a=x i∨a=y i∨a∈X)∧
      ∀ a,C.1.val a∉X→C.1.val (finRotate (l+5) a)∉X→
        markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead (l+4) π b C.1 a)=old i
  have load_bound {k:ℕ} (e:Fin k↪Fin N) (C:Fin k→MarkedWheel tail head ktail khead (l+4) π b H₀ HK)
      (hC:∀ j,Good (e j) (C j)) (hcap:∀ a∈X,markedFamilyRowLoad C a≤K) (a:V):
      markedFamilyRowLoad C a≤K+D₀:=by
    by_cases ha:a∈X
    · exact (hcap a ha).trans (Nat.le_add_right _ _)
    · have hh:markedFamilyRowLoad C a≤(Finset.univ.filter (fun i=>a=x i∨a=y i)).card:=by
        apply Finset.card_le_card_of_injOn e
        · intro j hj
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
          rcases (hC j).2.2.1 a (Finset.mem_filter.mp hj).2 with h|h|h
          · exact Or.inl h
          · exact Or.inr h
          · exact (ha h).elim
        · intro i _ j _ hij;exact e.injective hij
      exact (hh.trans (hend a)).trans (Nat.le_add_left _ _)
  have hp:∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→MarkedWheel tail head ktail khead (l+4) π b H₀ HK,
      (∀ j,Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))∧
      (∀ a∈X,markedFamilyRowLoad C a≤K)∧∀ u,markedFamilyHubLoad C u≤K:=by
    intro k
    induction k with
    | zero=>
      intro hk
      refine ⟨Fin.elim0,fun j=>Fin.elim0 j,fun i=>Fin.elim0 i,?_,?_⟩
      · intro a _;simp [markedFamilyRowLoad]
      · intro u;simp [markedFamilyHubLoad]
    | succ k ih=>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hC,hdis,hcap,hhub⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,by intro a b h;exact Fin.ext (congrArg (fun z:Fin N=>z.val) h)⟩
      let i:Fin N:=⟨k,by omega⟩
      have hr (a:V):markedFamilyRowLoad C a≤K+D₀:=load_bound e C hC hcap a
      let D:=markedFamilyRim C
      let S:=Finset.univ.filter (fun a=>K≤markedFamilyRowLoad C a)
      let B:=Finset.univ.filter (fun u=>K≤markedFamilyHubLoad C u)
      have hS:(S.card:ℝ)≤(N*(l+5):ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*S.card≤N*(l+5):=(markedFamilyRowLoad_saturated C K).trans
          (by simp only [Fintype.card_fin];exact Nat.mul_le_mul_right (l+5) hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hB:(B.card:ℝ)≤N/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*B.card≤N:=(markedFamilyHubLoad_saturated C K).trans
          (by simpa only [Fintype.card_fin] using hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hW:(((Xᶜ)∪S).card:ℝ)≤((Xᶜ).card:ℝ)+(N*(l+5):ℕ)/(K:ℝ):=by
        have hh:(((Xᶜ)∪S).card:ℝ)≤(Xᶜ).card+S.card:=by exact_mod_cast Finset.card_union_le _ _
        linarith only [hh,hS]
      have hJB:((J∪B).card:ℝ)≤(J.card:ℝ)+N/(K:ℝ):=by
        have hh:((J∪B).card:ℝ)≤J.card+B.card:=by exact_mod_cast Finset.card_union_le _ _
        linarith only [hh,hB]
      have hD:∀ a,(D.degree a:ℝ)≤4*(K+D₀:ℕ):=by
        intro a
        have hh:(D.degree a)≤4*(K+D₀):=(markedFamilyRim_degree hb C a).trans
          (by have h1:=hr a;have h2:=hr (π.symm a);omega)
        exact_mod_cast hh
      have hold:∀ j a,(C j).1.val a∈Xᶜ→(C j).1.val (finRotate (l+5) a)∈Xᶜ→
          markedPhysicalEdge tail head ktail khead π (markedCycleTypedEdge tail head ktail khead (l+4) π b (C j).1 a)=old (e j):=by
        intro j a ha hz;exact (hC j).2.2.2 a (Finset.mem_compl.mp ha) (Finset.mem_compl.mp hz)
      have hrootD:¬D.Adj (x i) (if t i then π (y i) else y i):=by
        apply marked_prescribed_arc_avoids_family hphys C (Xᶜ) (fun j=>old (e j)) hold (t i) (x i) (y i)
          (Finset.mem_compl.mpr (hx i)) (Finset.mem_compl.mpr (hy i)) (hroot i)
        intro j he
        have he':=congrArg (fun z:Fin N=>z.val) (hedge he)
        have hj:=j.isLt
        dsimp [e,i] at he';omega
      obtain ⟨p,W,hWcoord,hpW,hWu,hA,hWD⟩:=marked_rim_wheel_after_deletion Q hl D
        (4*(K+D₀:ℕ)) (by positivity) hD (t i) (x i) (y i) (hsep i) (hroot i) hrootD
        ((Xᶜ)∪S) (J∪B) (markedFamilySpokes C) (K+D₀)
        (fun a=>(markedFamilySpokes_row C a).trans (hr a))
        (by linarith only [hW,hbudget]) (by linarith only [hJB,hhbudget])
      have hrows:=marked_two_root_rows p (x i) (y i) _ W hWcoord
      have hfree:∀ a,p a∈X:=by
        intro a;by_contra hn;exact hpW a (Finset.mem_union_left _ (Finset.mem_compl.mpr hn))
      have hWG:Good i W:=by
        refine ⟨fun h=>hWu (Finset.mem_union_left _ h),marked_two_root_contains_arc (by omega) p (x i) (y i) (t i) W hWcoord,?_,?_⟩
        · intro a ha
          rw [hrows] at ha
          rcases Finset.mem_insert.mp ha with h|h
          · exact Or.inl h
          · rcases Finset.mem_insert.mp h with h|h
            · exact Or.inr (Or.inl h)
            · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp h
              exact Or.inr (Or.inr (hfree z))
        · intro a ha hz
          exact marked_two_root_wheel_old_arc (l+2) (by omega) p (x i) (y i) (t i) (Xᶜ)
            (fun z hz=>Finset.mem_compl.mp hz (hfree z)) W hWcoord a
            (Finset.mem_compl.mpr ha) (Finset.mem_compl.mpr hz)
      have hcross (j:Fin k):Disjoint (markedWheelPhysicalResources (C j)) (markedWheelPhysicalResources W):=by
        apply Finset.disjoint_left.mpr
        intro z hz hzW
        cases z with
        | inl z=>
          rw [markedWheelPhysicalResources_rim] at hz hzW
          have hc:z.card=2:=by
            obtain ⟨a,_,ha⟩:=Finset.mem_image.mp hz
            rw [←ha]
            exact markedCycle_physical_edge_card tail head ktail khead (l+4) π b (by omega) hb (C j).1 a
          obtain ⟨a,d,had,rfl⟩:=Finset.card_eq_two.mp hc
          exact disjoint_graphs_no_common_edge _ _ hWD a d ⟨had,hzW⟩ (SimpleGraph.iSup_adj.mpr ⟨j,had,hz⟩)
        | inr au=>
          rw [markedWheelPhysicalResources_spoke] at hz hzW
          exact hA au.1 hzW.2 ⟨j,hz.1.trans hzW.1.symm,hz.2⟩
      refine ⟨Fin.snoc C W,?_,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hWG
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j q
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun q'=>?_) q
          · intro h;exact (h rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross q').symm
        · refine Fin.lastCases ?_ (fun q'=>?_) q
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro h;simpa only [Fin.snoc_castSucc] using hdis j' q' (fun he=>h (congrArg Fin.castSucc he))
      · intro a ha
        rw [markedFamilyRowLoad_snoc]
        by_cases haw:a∈markedWheelRows W
        · rw [if_pos haw]
          have haS:a∉S:=by
            rw [hrows] at haw
            rcases Finset.mem_insert.mp haw with h|h
            · exact (hx i (h ▸ ha)).elim
            · rcases Finset.mem_insert.mp h with h|h
              · exact (hy i (h ▸ ha)).elim
              · obtain ⟨z,_,rfl⟩:=Finset.mem_image.mp h
                exact fun hs=>hpW z (Finset.mem_union_right _ hs)
          have hh:markedFamilyRowLoad C a<K:=by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using haS
          omega
        · rw [if_neg haw,Nat.add_zero];exact hcap a ha
      · intro u
        rw [markedFamilyHubLoad_snoc]
        by_cases hu:W.2.val=u
        · rw [if_pos hu]
          have huB:u∉B:=by intro huB;exact hWu (Finset.mem_union_right _ (hu ▸ huB))
          have hh:markedFamilyHubLoad C u<K:=by simpa only [B,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using huB
          omega
        · rw [if_neg hu,Nat.add_zero];exact hhub u
  obtain ⟨C,hC,hdis,hcap,hhub⟩:=hp N le_rfl
  have hr:∀ a,markedFamilyRowLoad C a≤K+D₀:=load_bound (Function.Embedding.refl _) C hC hcap
  refine ⟨C,hC,hdis,hcap,hhub,?_,?_,?_⟩
  · intro a
    apply (markedFamilyRim_degree hb C a).trans
    have h1:=hr a;have h2:=hr (π.symm a);omega
  · intro a;exact (markedFamilySpokes_row C a).trans (hr a)
  · intro u;exact (markedFamilySpokes_column C u).trans (Nat.mul_le_mul_right (l+5) (hhub u))

end Oberwolfach
