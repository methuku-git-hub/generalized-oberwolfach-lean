module

public import Oberwolfach.SeparatedDirectedPrefixes

@[expose] public section

/-! A fixed-length directed path between two supplied attachment vertices.
The last internal vertex uses the actual intersection of its incoming and
outgoing requirements. Position-specific candidate sets retain spoke types. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

 theorem separated_directed_path (F:SimpleGraph V)
    (D:ℕ→V→V→Prop) (A:ℕ→Finset V) (W Z:Finset V)
    (d c:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (l:ℕ) (x y:V) (hxy:x≠y) (hxyF:¬F.Adj x y)
    (hxA:x∈A 0) (hyA:y∈A (l+2)) (hxW:x∉W) (hyW:y∉W)
    (hxZ:x∉Z) (hyZ:y∉Z) (hxF:∀ z∈Z,¬F.Adj x z) (hyF:∀ z∈Z,¬F.Adj y z)
    (hcount:∀ i<l,∀ v∈A i,c≤(((A (i+1)).filter (D i v)).card:ℝ))
    (hcommon:∀ v∈A l,v≠y→c≤(((A (l+1)).filter (fun z=>D l v z∧D (l+1) z y)).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+l+4)*(d+1)<c):
    ∃ p:Fin (l+3)↪V,p 0=x∧p (Fin.last (l+2))=y∧
      (∀ i,p i∈A i.val∧p i∉W∧p i∉Z∧∀ z∈Z,¬F.Adj (p i) z)∧
      (∀ i:Fin (l+2),D i.val (p i.castSucc) (p i.succ))∧
      ∀ i j,¬F.Adj (p i) (p j):=by
  have hins:((insert y Z).card:ℝ)≤Z.card+1:=by exact_mod_cast Finset.card_insert_le y Z
  have hbudget':W.card+(((insert y Z).card:ℝ)+l+1)*(d+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right hins (show 0≤d+1 by linarith)
    nlinarith only [hh,hbudget,hd]
  obtain ⟨p,hp0,hpA,hpD,hpF⟩:=separated_directed_prefix F D A W (insert y Z) d c hd hF l x hxA hxW
    (by simp [hxy,hxZ]) (by intro z hz;rcases Finset.mem_insert.mp hz with rfl|hz;exact hxyF;exact hxF z hz)
    hcount hbudget'
  let S:Finset V:=Finset.univ.image p
  have hS:S.card=l+1:=by
    dsimp only [S]
    rw [Finset.card_image_of_injective _ p.injective,Finset.card_univ,Fintype.card_fin]
  have hZS:(((insert y Z)∪S).card:ℝ)≤Z.card+l+2:=by
    have hh:(((insert y Z)∪S).card:ℝ)≤(insert y Z).card+S.card:=by exact_mod_cast Finset.card_union_le (insert y Z) S
    rw [hS] at hh
    push_cast at hh
    linarith
  have hchoice:W.card+(((insert y Z)∪S).card:ℝ)*(d+1)<c:=by
    have hh:=mul_le_mul_of_nonneg_right hZS (show 0≤d+1 by linarith)
    nlinarith only [hh,hbudget,hd]
  obtain ⟨z,hz,hzW,hzZS,hzF⟩:=candidate_vertex_avoiding F
    ((A (l+1)).filter (fun z=>D l (p (Fin.last l)) z∧D (l+1) z y)) W ((insert y Z)∪S)
    d c hF (hcommon _ (hpA (Fin.last l)).1
      (fun he=>(hpA (Fin.last l)).2.2.1 (by simp [he]))) hchoice
  have hzout:z∉Set.range p:=by
    rintro ⟨i,hi⟩
    exact hzZS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩))
  let q:Fin (l+2)↪V:=⟨Fin.snoc p z,Fin.snoc_injective_of_injective p.injective hzout⟩
  have hqold (i:Fin (l+1)):q i.castSucc=p i:=by simp only [q,Function.Embedding.coeFn_mk,Fin.snoc_castSucc]
  have hqlast:q (Fin.last (l+1))=z:=by simp only [q,Function.Embedding.coeFn_mk,Fin.snoc_last]
  have hzy:z≠y:=fun h=>hzZS (Finset.mem_union_left _ (by simp [h]))
  have hyout:y∉Set.range q:=by
    rintro ⟨i,hi⟩
    revert hi
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [hqlast];exact hzy
    · rw [hqold]
      intro h
      exact (hpA j).2.2.1 (by simp [h])
  let t:Fin (l+3)↪V:=⟨Fin.snoc q y,Fin.snoc_injective_of_injective q.injective hyout⟩
  have htold (i:Fin (l+2)):t i.castSucc=q i:=by simp only [t,Function.Embedding.coeFn_mk,Fin.snoc_castSucc]
  have htlast:t (Fin.last (l+2))=y:=by simp only [t,Function.Embedding.coeFn_mk,Fin.snoc_last]
  have hqA (i:Fin (l+2)):q i∈A i.val∧q i∉W∧q i∉Z∧∀ w∈Z,¬F.Adj (q i) w:=by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [hqlast]
      exact ⟨(Finset.mem_filter.mp hz).1,hzW,
        fun h=>hzZS (Finset.mem_union_left _ (Finset.mem_insert_of_mem h)),
        fun w hw=>hzF w (Finset.mem_union_left _ (Finset.mem_insert_of_mem hw))⟩
    · rw [hqold]
      exact ⟨(hpA j).1,(hpA j).2.1,fun h=>(hpA j).2.2.1 (Finset.mem_insert_of_mem h),
        fun w hw=>(hpA j).2.2.2 w (Finset.mem_insert_of_mem hw)⟩
  have hqD (i:Fin (l+1)):D i.val (q i.castSucc) (q i.succ):=by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [show (Fin.last l).succ=Fin.last (l+1) from rfl,hqold,hqlast]
      exact (Finset.mem_filter.mp hz).2.1
    · rw [hqold,show j.castSucc.succ=j.succ.castSucc from rfl,hqold]
      exact hpD j
  have hqF (i j:Fin (l+2)):¬F.Adj (q i) (q j):=by
    refine Fin.lastCases ?_ (fun a=>?_) i
    · rw [hqlast]
      refine Fin.lastCases ?_ (fun b=>?_) j
      · rw [hqlast];exact F.loopless.irrefl _
      · rw [hqold]
        exact hzF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩))
    · rw [hqold]
      refine Fin.lastCases ?_ (fun b=>?_) j
      · rw [hqlast]
        exact fun h=>hzF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)) h.symm
      · rw [hqold];exact hpF a b
  have hqyF (i:Fin (l+2)):¬F.Adj (q i) y:=by
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [hqlast];exact hzF y (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
    · rw [hqold];exact (hpA j).2.2.2 y (Finset.mem_insert_self _ _)
  refine ⟨t,(htold 0).trans ((hqold 0).trans hp0),htlast,?_,?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [htlast];exact ⟨hyA,hyW,hyZ,hyF⟩
    · rw [htold];exact hqA j
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · rw [show (Fin.last (l+1)).succ=Fin.last (l+2) from rfl,htold,htlast,hqlast]
      exact (Finset.mem_filter.mp hz).2.2
    · rw [htold,show j.castSucc.succ=j.succ.castSucc from rfl,htold]
      exact hqD j
  · intro i j
    refine Fin.lastCases ?_ (fun a=>?_) i
    · rw [htlast]
      refine Fin.lastCases ?_ (fun b=>?_) j
      · rw [htlast];exact F.loopless.irrefl _
      · rw [htold];exact fun h=>hqyF b h.symm
    · rw [htold]
      refine Fin.lastCases ?_ (fun b=>?_) j
      · rw [htlast];exact hqyF a
      · rw [htold];exact hqF a b

end Oberwolfach
