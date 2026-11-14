module

public import Oberwolfach.SeparatedCandidateVertices
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! A directed path prefix with a specified relation at each position.
Candidate sets may impose different spoke types at different positions.
No relation is symmetrised, and every new row is excluded from the actual
previous labels and their conflict neighbourhoods. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 9000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V:Type} [Fintype V] [DecidableEq V]

 theorem separated_directed_prefix (F:SimpleGraph V)
    (D:ℕ→V→V→Prop) (A:ℕ→Finset V) (W Z:Finset V)
    (d c:ℝ) (hd:0≤d) (hF:∀ v,(F.degree v:ℝ)≤d)
    (k:ℕ) (x:V) (hxA:x∈A 0) (hxW:x∉W) (hxZ:x∉Z)
    (hxF:∀ z∈Z,¬F.Adj x z)
    (hcount:∀ i<k,∀ v∈A i,c≤(((A (i+1)).filter (D i v)).card:ℝ))
    (hbudget:W.card+((Z.card:ℝ)+k+1)*(d+1)<c):
    ∃ p:Fin (k+1)↪V,p 0=x∧
      (∀ i,p i∈A i.val∧p i∉W∧p i∉Z∧∀ z∈Z,¬F.Adj (p i) z)∧
      (∀ i:Fin k,D i.val (p i.castSucc) (p i.succ))∧
      ∀ i j,¬F.Adj (p i) (p j):=by
  induction k with
  | zero=>
    let p:Fin 1↪V:=⟨fun _=>x,fun _ _ _=>Subsingleton.elim _ _⟩
    refine ⟨p,rfl,?_,?_,?_⟩
    · intro i
      have hi:i=0:=by apply Fin.ext;omega
      subst i
      exact ⟨hxA,hxW,hxZ,hxF⟩
    · intro i;exact Fin.elim0 i
    · intro i j;exact F.loopless.irrefl _
  | succ k ih=>
    have hbudget':W.card+((Z.card:ℝ)+k+1)*(d+1)<c:=by
      push_cast at hbudget
      nlinarith only [hbudget,hd]
    obtain ⟨p,hp0,hpA,hpD,hpF⟩:=ih (fun i hi=>hcount i (by omega)) hbudget'
    let S:Finset V:=Finset.univ.image p
    have hS:S.card=k+1:=by
      dsimp only [S]
      rw [Finset.card_image_of_injective _ p.injective,Finset.card_univ,Fintype.card_fin]
    have hZS:((Z∪S).card:ℝ)≤Z.card+(k+1:ℕ):=by
      exact_mod_cast (Finset.card_union_le Z S).trans_eq (by rw [hS])
    have hchoice:W.card+((Z∪S).card:ℝ)*(d+1)<c:=by
      have hh:=mul_le_mul_of_nonneg_right hZS (show 0≤d+1 by linarith)
      push_cast at hh hbudget
      nlinarith only [hh,hbudget,hd]
    obtain ⟨y,hy,hyW,hyZS,hyF⟩:=candidate_vertex_avoiding F ((A (k+1)).filter (D k (p (Fin.last k))))
      W (Z∪S) d c hF (hcount k (by omega) _ (hpA (Fin.last k)).1) hchoice
    have hyp:y∉Set.range p:=by
      rintro ⟨i,hi⟩
      exact hyZS (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩))
    let q:Fin (k+2)↪V:=⟨Fin.snoc p y,Fin.snoc_injective_of_injective p.injective hyp⟩
    have hqold (i:Fin (k+1)):q i.castSucc=p i:=by simp only [q,Function.Embedding.coeFn_mk,Fin.snoc_castSucc]
    have hqlast:q (Fin.last (k+1))=y:=by simp only [q,Function.Embedding.coeFn_mk,Fin.snoc_last]
    refine ⟨q,?_,?_,?_,?_⟩
    · exact (hqold 0).trans hp0
    · intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · rw [hqlast]
        exact ⟨(Finset.mem_filter.mp hy).1,hyW,
          fun hz=>hyZS (Finset.mem_union_left _ hz),
          fun z hz=>hyF z (Finset.mem_union_left _ hz)⟩
      · rw [hqold]
        exact hpA j
    · intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · rw [show (Fin.last k).succ=Fin.last (k+1) from rfl,hqold,hqlast]
        exact (Finset.mem_filter.mp hy).2
      · rw [hqold,show j.castSucc.succ=j.succ.castSucc from rfl,hqold]
        exact hpD j
    · intro i j
      refine Fin.lastCases ?_ (fun a=>?_) i
      · rw [hqlast]
        refine Fin.lastCases ?_ (fun b=>?_) j
        · rw [hqlast];exact F.loopless.irrefl _
        · rw [hqold]
          exact hyF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩))
      · rw [hqold]
        refine Fin.lastCases ?_ (fun b=>?_) j
        · rw [hqlast]
          exact fun h=>hyF _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩)) h.symm
        · rw [hqold];exact hpF a b

end Oberwolfach
