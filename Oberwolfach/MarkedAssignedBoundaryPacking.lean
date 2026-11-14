module

public import Oberwolfach.MarkedAssignedRowPacking
public import Oberwolfach.MarkedAssignedRowInDomain
public import Oberwolfach.MarkedFreeRimAndSpokeDisjointness
public import Oberwolfach.GreedyGraphCandidates

@[expose] public section

/-! Complete all assigned boundary paths. Hubs and outside roots may repeat;
the prescribed root arcs, root spokes and endpoint spokes are checked as
physical resources. Every unassigned spoke avoids the entire reserved
endpoint relation, including the endpoints of paths chosen later. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 25000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U E T:Type} [Fintype V] [Fintype U] [DecidableEq V] [DecidableEq U]
    {tail head:E→V} {ktail khead:T→V} {H₀ HK:V→U→Prop}
    {π:Equiv.Perm V} {b l:ℕ} {c:ℝ}

theorem marked_assigned_boundary_packing
    (X:Finset V) (Q:MarkedBoundaryExtensionCounts tail head ktail khead H₀ HK X c)
    (hl:2≤l) (hb:1≤b) (hX:∀ x,π x∈X↔x∈X)
    (N K D₀ D₁ D₂:ℕ) (hK:0<K)
    (v a z:Fin N→V) (u:Fin N→U) (jin jout:Fin N→Bool)
    (hv:∀ i,v i∉X) (ha:∀ i,a i∈X) (hz:∀ i,z i∈X)
    (htypes:∀ i,¬(jin i=true∧jout i=true))
    (haz:∀ i,¬PermutationClose π b (a i) (z i))
    (hav:∀ i,¬PermutationClose π b (a i) (v i)) (hzv:∀ i,¬PermutationClose π b (z i) (v i))
    (haH:∀ i,if jout i then HK (a i) (u i) else H₀ (a i) (u i))
    (hzH:∀ i,H₀ (z i) (u i)) (hroot:∀ i,if jin i then HK (v i) (u i) else H₀ (v i) (u i))
    (hopen:∀ i,markedArcPresent tail head ktail khead (jout i) (v i) (a i))
    (hclose:∀ i,markedArcPresent tail head ktail khead (jin i) (z i) (v i))
    (hroots:∀ i j,i≠j→Disjoint (markedRowRootRims π (v i) (a i) (z i) (jin i) (jout i))
      (markedRowRootRims π (v j) (a j) (z j) (jin j) (jout j)))
    (hrootspokes:Function.Injective (fun i=>(v i,u i)))
    (hend:∀ x,(Finset.univ.filter (fun i=>x=a i∨x=z i)).card≤D₀)
    (hhub:∀ w,(Finset.univ.filter (fun i=>u i=w)).card≤D₁)
    (R:V→U→Prop) (hRa:∀ i,R (a i) (u i)) (hRz:∀ i,R (z i) (u i))
    (hR:∀ w,(Finset.univ.filter (fun x=>R x w)).card≤D₂)
    (hends:∀ i j,i≠j→u i=u j→Disjoint ({a i,z i}:Finset V) {a j,z j})
    (G:SimpleGraph V) (hGX:GraphSupportedOn X G) (δ:ℝ) (hδ:0≤δ)
    (hG:∀ x,(G.degree x:ℝ)≤δ)
    (hbudget:(N*(l+4):ℕ)/(K:ℝ)+D₂+(D₁*(l+4):ℕ)+
      (l+5)*(2*b+1)+2*(δ+4*(K+D₀:ℕ))<c):
    ∃ C:Fin N→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ i,(C i).2.val=u i∧∃ p:Fin (l+3)↪V,
        p 0=a i∧p (Fin.last (l+2))=z i∧
        (∀ j,(C i).1.val j=Fin.cons (α:=fun _=>V) (v i) p (markedAssignedRowOrder (l+3) (jin i) (jout i) j))∧
        (∀ j,p j∈X)∧
        (∀ x∈markedWheelRows (C i),x∈X→R x (u i)→x=a i∨x=z i)∧Disjoint (markedWheelRimGraph (C i)) G)∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))∧
      (∀ x∈X,markedFamilyFreeRowLoad C a z x≤K)∧
      (∀ x,(spanningRestriction (markedFamilyRim C) X).degree x≤4*(K+D₀))∧
      (∀ x∈X,(Finset.univ.filter (markedFamilySpokes C x)).card≤K+D₀)∧
      (∀ w,(Finset.univ.filter (fun x=>markedFamilySpokes C x w)).card≤D₁*(l+4)) := by
  let Good (i:Fin N) (C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK):=
    C.2.val=u i∧∃ p:Fin (l+3)↪V,p 0=a i∧p (Fin.last (l+2))=z i∧
      (∀ j,C.1.val j=Fin.cons (α:=fun _=>V) (v i) p (markedAssignedRowOrder (l+3) (jin i) (jout i) j))∧
      (∀ j,p j∈X)∧(∀ x∈markedWheelRows C,x∈X→R x (u i)→x=a i∨x=z i)∧Disjoint (markedWheelRimGraph C) G
  have forced_bound {k:ℕ} (e:Fin k↪Fin N) (x:V):
      (Finset.univ.filter (fun j=>x=a (e j)∨x=z (e j))).card≤D₀:=by
    apply le_trans _ (hend x)
    apply Finset.card_le_card_of_injOn e
    · intro j hj;exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij;exact e.injective hij
  have hub_bound {k:ℕ} (e:Fin k↪Fin N)
      (C:Fin k→MarkedWheel tail head ktail khead (l+3) π b H₀ HK)
      (hC:∀ j,Good (e j) (C j)) (w:U):markedFamilyHubLoad C w≤D₁:=by
    apply le_trans _ (hhub w)
    apply Finset.card_le_card_of_injOn e
    · intro j hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hC j).1.symm.trans (Finset.mem_filter.mp hj).2⟩
    · intro i _ j _ hij;exact e.injective hij
  have rows_good {i:Fin N} {C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK}
      (hC:Good i C):∀ x∈markedWheelRows C,x=v i∨x∈X:=by
    obtain ⟨hCu,p,hp0,hplast,hcoord,hpX,hres,hG⟩:=hC
    rw [marked_one_root_rows p (v i) _ C hcoord]
    intro x hx
    rcases Finset.mem_insert.mp hx with he|he
    · exact Or.inl he
    · obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp he;exact Or.inr (hpX j)
  have reserve_good {i:Fin N} {C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK}
      (hC:Good i C):∀ x∈markedWheelRows C,x∈X→R x (u i)→x=a i∨x=z i:=by
    obtain ⟨_,p,_,_,_,_,hres,_⟩:=hC;exact hres
  have classify {i:Fin N} {C:MarkedWheel tail head ktail khead (l+3) π b H₀ HK}
      (hC:Good i C):∀ e∈markedCyclePhysicalEdges tail head ktail khead (l+3) π b C.1,
        e⊆X∨e∈markedRowRootRims π (v i) (a i) (z i) (jin i) (jout i):=by
    obtain ⟨hCu,p,hp0,hplast,hcoord,hpX,_,_⟩:=hC
    have hh:=marked_assigned_row_rim_classification (by omega:2≤l+2) p (v i) (jin i) (jout i)
      (htypes i) X (fun x hx=>(hX x).mpr hx) hpX C hcoord
    simpa only [hp0,hplast] using hh
  have hp:∀ k:ℕ,∀ hk:k≤N,∃ C:Fin k→MarkedWheel tail head ktail khead (l+3) π b H₀ HK,
      (∀ j,Good ⟨j.val,lt_of_lt_of_le j.isLt hk⟩ (C j))∧
      (∀ i j,i≠j→Disjoint (markedWheelPhysicalResources (C i)) (markedWheelPhysicalResources (C j)))∧
      ∀ x∈X,markedFamilyFreeRowLoad C
        (fun j=>a ⟨j.val,lt_of_lt_of_le j.isLt hk⟩) (fun j=>z ⟨j.val,lt_of_lt_of_le j.isLt hk⟩) x≤K:=by
    intro k
    induction k with
    | zero=>
      intro hk;refine ⟨Fin.elim0,fun j=>Fin.elim0 j,fun i=>Fin.elim0 i,?_⟩
      intro x hx;simp [markedFamilyFreeRowLoad]
    | succ k ih=>
      intro hk
      have hkN:k≤N:=by omega
      obtain ⟨C,hC,hdis,hcap⟩:=ih hkN
      let e:Fin k↪Fin N:=⟨fun j=>⟨j.val,lt_of_lt_of_le j.isLt hkN⟩,
        by intro a b h;exact Fin.ext (congrArg (fun z:Fin N=>z.val) h)⟩
      let i:Fin N:=⟨k,by omega⟩
      have hne (j:Fin k):e j≠i:=by intro he;have ht:=congrArg (fun t:Fin N=>t.val) he;have hj:=j.isLt;dsimp [e,i] at ht;omega
      let D:=G⊔spanningRestriction (markedFamilyRim C) X
      let S:=Finset.univ.filter (fun x=>K≤markedFamilyFreeRowLoad C (a∘e) (z∘e) x)
      let Rᵤ:=Finset.univ.filter (fun x=>R x (u i))
      let Pᵤ:=Finset.univ.filter (fun x=>markedFamilySpokes C x (u i))
      let W:=(S∪(Rᵤ∪Pᵤ))\{a i,z i}
      have hS:(S.card:ℝ)≤(N*(l+4):ℕ)/(K:ℝ):=by
        apply (le_div_iff₀ (Nat.cast_pos.mpr hK)).mpr
        have hh:K*S.card≤N*(l+4):=(markedFamilyFreeRowLoad_saturated C (a∘e) (z∘e) K).trans
          (by simp only [Fintype.card_fin];exact Nat.mul_le_mul_right (l+4) hkN)
        exact_mod_cast (by simpa only [Nat.mul_comm] using hh)
      have hP:Pᵤ.card≤D₁*(l+4):=(markedFamilySpokes_column C (u i)).trans
        (Nat.mul_le_mul_right (l+4) (hub_bound e C hC (u i)))
      have hW:(W.card:ℝ)≤(N*(l+4):ℕ)/(K:ℝ)+D₂+(D₁*(l+4):ℕ):=by
        have hh:W.card≤S.card+(Rᵤ.card+Pᵤ.card):=
          (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_union_le _ _).trans
            (Nat.add_le_add_left (Finset.card_union_le _ _) _))
        have hh':(W.card:ℝ)≤S.card+(D₂+(D₁*(l+4):ℕ)):=by
          exact_mod_cast hh.trans (Nat.add_le_add_left (Nat.add_le_add (hR (u i)) hP) _)
        linarith only [hh',hS]
      have hD:∀ x,(D.degree x:ℝ)≤δ+4*(K+D₀:ℕ):=by
        intro x
        have hr:=marked_free_rim_degree C (a∘e) (z∘e) hb X hX K D₀ hcap (forced_bound e) x
        have hd:D.degree x≤G.degree x+(spanningRestriction (markedFamilyRim C) X).degree x:=by convert graph_degree_sup_le G (spanningRestriction (markedFamilyRim C) X) x using 1 <;> congr!
        have hd':(D.degree x:ℝ)≤G.degree x+(4*(K+D₀):ℕ):=by exact_mod_cast hd.trans (Nat.add_le_add_left (hr) _)
        push_cast at hd'
        push_cast
        linarith only [hd',hG x]
      have hDX:GraphSupportedOn X D:=by
        intro x y hxy
        rcases hxy with hg|hp
        · exact hGX x y hg
        · exact ((spanningRestriction_adj _ _ _ _).mp hp).2
      have haW:a i∉W:=by simp [W]
      have hzW:z i∉W:=by simp [W]
      have haZ:a i∉({v i}:Finset V):=by intro h;exact hav i (Or.inl (Finset.mem_singleton.mp h))
      have hzZ:z i∉({v i}:Finset V):=by intro h;exact hzv i (Or.inl (Finset.mem_singleton.mp h))
      have hoD:¬D.Adj (v i) (if jout i then π (a i) else a i):=by intro h;exact hv i (hDX _ _ h).1
      have hcD:¬D.Adj (z i) (if jin i then π (v i) else v i):=by
        intro h;have hh:=(hDX _ _ h).2
        cases hj:jin i
        · rw [hj] at hh;exact hv i hh
        · rw [hj] at hh;exact hv i ((hX (v i)).mp hh)
      obtain ⟨p,B,hp0,hplast,hBu,hB,hlocal,hsep,hBD⟩:=marked_assigned_row_in_domain X Q hl D
        (δ+4*(K+D₀:ℕ)) (by positivity) (by intro x;convert hD x using 1 <;> congr!) (v i) (a i) (z i) (u i) (jin i) (jout i) (htypes i)
        W {v i} (by simp) (ha i) (hz i) haW hzW haZ hzZ (haz i)
        (by intro x hx;rw [Finset.mem_singleton.mp hx];exact hav i)
        (by intro x hx;rw [Finset.mem_singleton.mp hx];exact hzv i)
        (haH i) (hzH i) (hroot i) (hopen i) (hclose i) hoD hcD
        (by simp only [Finset.card_singleton,Nat.cast_one];linarith only [hW,hbudget])
      have hpX:∀ j,p j∈X:=fun j=>(hlocal j).1
      have havB:=fun j=>(hlocal j).2
      have hres:∀ x∈markedWheelRows B,x∈X→R x (u i)→x=a i∨x=z i:=by
        intro x hx hxX hxR
        by_contra hne
        rw [marked_one_root_rows p (v i) _ B hB] at hx
        rcases Finset.mem_insert.mp hx with he|he
        · exact hv i (he ▸ hxX)
        · obtain ⟨j,_,he⟩:=Finset.mem_image.mp he
          apply (havB j).1
          rw [he]
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxR⟩)),by simpa using hne⟩
      have hBG:Disjoint (markedWheelRimGraph B) G:=hBD.mono_right le_sup_left
      have hGood:Good i B:=⟨hBu,p,hp0,hplast,hB,hpX,hres,hBG⟩
      have hspokeDis (j:Fin k) (hubs:(C j).2.val=B.2.val):Disjoint (markedWheelRows (C j)) (markedWheelRows B):=by
        have huij:u (e j)=u i:=(hC j).1.symm.trans (hubs.trans hBu)
        apply Finset.disjoint_left.mpr
        intro x hxOld hxNew
        rcases rows_good hGood x hxNew with he|hxX
        · rcases rows_good (hC j) x hxOld with ho|ho
          · have hei:e j=i:=hrootspokes (Prod.ext (ho.symm.trans he) huij)
            exact hne j hei
          · exact hv i (he ▸ ho)
        · have hnot:x≠a i∧x≠z i:=by
            constructor
            · intro he
              have hr:R x (u (e j)):=by rw [huij,he];exact hRa i
              have hs:=reserve_good (hC j) x hxOld hxX hr
              exact Finset.disjoint_left.mp (hends (e j) i (hne j) huij)
                (by simpa [e] using hs) (by simp [he])
            · intro he
              have hr:R x (u (e j)):=by rw [huij,he];exact hRz i
              have hs:=reserve_good (hC j) x hxOld hxX hr
              exact Finset.disjoint_left.mp (hends (e j) i (hne j) huij)
                (by simpa [e] using hs) (by simp [he])
          rw [marked_one_root_rows p (v i) _ B hB] at hxNew
          rcases Finset.mem_insert.mp hxNew with he|he
          · exact hv i (he ▸ hxX)
          · obtain ⟨t,_,he⟩:=Finset.mem_image.mp he
            apply (havB t).1
            rw [he]
            have hp:x∈Pᵤ:=Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨j,(hC j).1.trans huij,hxOld⟩⟩
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_union_right _ hp),by simpa using hnot⟩
      have hcross:∀ j,Disjoint (markedWheelPhysicalResources (C j)) (markedWheelPhysicalResources B):=by
        apply marked_free_rim_and_spoke_extension_disjoint (by omega) hb C B X
          (fun j=>markedRowRootRims π (v (e j)) (a (e j)) (z (e j)) (jin (e j)) (jout (e j)))
          (markedRowRootRims π (v i) (a i) (z i) (jin i) (jout i))
        · intro j;exact classify (hC j)
        · exact classify hGood
        · intro j;exact marked_row_root_rim_not_inside X hX (v (e j)) _ _ (hv (e j)) _ _
        · intro j;exact hroots (e j) i (hne j)
        · exact hspokeDis
        · exact hBD.mono_right le_sup_right
      refine ⟨Fin.snoc C B,?_,?_,?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun j=>?_) j
        · simpa only [Fin.snoc_last,Fin.val_last,i] using hGood
        · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hC j
      · intro j q
        refine Fin.lastCases ?_ (fun j'=>?_) j
        · refine Fin.lastCases ?_ (fun q'=>?_) q
          · intro h;exact (h rfl).elim
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using (hcross q').symm
        · refine Fin.lastCases ?_ (fun q'=>?_) q
          · intro _;simpa only [Fin.snoc_last,Fin.snoc_castSucc] using hcross j'
          · intro h;simpa only [Fin.snoc_castSucc] using hdis j' q' (fun he=>h (congrArg Fin.castSucc he))
      · intro x hx
        have haeq:(fun j:Fin (k+1)=>a ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc (a∘e) (a i):=by
          funext j;refine Fin.lastCases ?_ (fun j=>?_) j <;> simp [e,i]
        have hzeq:(fun j:Fin (k+1)=>z ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)=Fin.snoc (z∘e) (z i):=by
          funext j;refine Fin.lastCases ?_ (fun j=>?_) j <;> simp [e,i]
        rw [haeq,hzeq,markedFamilyFreeRowLoad_snoc]
        by_cases hfree:x∈markedWheelRows B∧x≠a i∧x≠z i
        · rw [if_pos hfree]
          have hxS:x∉S:=by
            intro hs
            rw [marked_one_root_rows p (v i) _ B hB] at hfree
            rcases Finset.mem_insert.mp hfree.1 with he|he
            · exact hv i (he ▸ hx)
            · obtain ⟨j,_,he⟩:=Finset.mem_image.mp he
              apply (havB j).1
              rw [he]
              exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hs,by simpa using hfree.2⟩
          have hh:markedFamilyFreeRowLoad C (a∘e) (z∘e) x<K:=by
            simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and,not_le] using hxS
          omega
        · rw [if_neg hfree,Nat.add_zero];exact hcap x hx
  obtain ⟨C,hC,hdis,hcap⟩:=hp N le_rfl
  refine ⟨C,hC,hdis,hcap,marked_free_rim_degree C a z hb X hX K D₀ hcap hend,?_,?_⟩
  · intro x hx
    exact (markedFamilySpokes_row C x).trans ((markedFamilyRowLoad_le_free_add_forced C a z x).trans
      (Nat.add_le_add (hcap x hx) (hend x)))
  · intro w
    exact (markedFamilySpokes_column C w).trans (Nat.mul_le_mul_right (l+4)
      (hub_bound (Function.Embedding.refl (Fin N)) C hC w))

end Oberwolfach
