module

public import Oberwolfach.OrdinaryCommonPaths

@[expose] public section

/-! Each counted common path yields both actual replacement cycles, with
the original forbidden-pair restrictions and the same free vertex set. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}

theorem ordinary_common_path_cycle (Q F : SimpleGraph V) (T : Finset V) (hm : 2 ≤ m)
    (x y z : V) (hz : z=x ∨ z=y) (hzT : z∈T) (f : Fin m→V)
    (hf : SparseGreedyGood Q F T {x,y} (ordinaryPathRequirements m x y) f) :
    ∃ C : LocalOrdinaryCycle Q F T (m+1),localOrdinaryVertices C=insert z (Finset.univ.image f) := by
  let g : Fin m→V := fun i=>f (commonPathOrder m hm i)
  have hginj : Function.Injective g := hf.1.comp (commonPathOrder m hm).injective
  have hout : z∉Set.range g := by
    rintro ⟨i,hi⟩
    have hh := (hf.2.1 (commonPathOrder m hm i)).2
    apply hh
    change f (commonPathOrder m hm i)=z at hi
    rw [hi]
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
  let e : Fin (m+1) ↪ V := ⟨Fin.cons (α:=fun _=>V) z g,Fin.cons_injective_of_injective hout hginj⟩
  have e0 : e 0=z := rfl
  have epos (i : Fin (m+1)) (hi : 0 < i.val) :
      e i=f ⟨transferColumnOrder (m+1) i.val,by
        simpa only [Nat.add_sub_cancel] using transferColumnOrder_bound (m+1) i.val (by omega) hi i.isLt⟩ := by
    cases i using Fin.cases with
    | zero => simp at hi
    | succ j => rfl
  have hQ : ∀ i j,(SimpleGraph.cycleGraph (m+1)).Adj i j → Q.Adj (e i) (e j) := by
    have step (i j : Fin (m+1)) (hij : i.val+1=j.val) : Q.Adj (e i) (e j) := by
      by_cases hi0 : i.val=0
      · have hi : i=0 := Fin.ext hi0
        have hj1 : j.val=1 := by omega
        rw [hi,e0,epos j (by omega)]
        apply ordinaryCommonPath_endpoint Q F T x y f hf hm z hz
        left;simp only [transferColumnOrder,hj1,ite_true]
      · rw [epos i (by omega),epos j (by omega)]
        convert ordinaryCommonPath_step Q F T x y f hf hm i.val (by omega) (by have hj:=j.isLt;omega) using 1
        congr 2;rw [hij]
    have wrap (i j : Fin (m+1)) (hi : i.val=0) (hj : j.val=(m+1)-1) : Q.Adj (e i) (e j) := by
      rw [show i=0 from Fin.ext hi,e0,epos j (by omega)]
      apply ordinaryCommonPath_endpoint Q F T x y f hf hm z hz
      right;simp only [transferColumnOrder];split_ifs <;> omega
    intro i j hij
    rcases cycleGraph_adj_natural_cases (m+1) (by omega) i j hij with h|h|⟨hi,hj⟩|⟨hj,hi⟩
    · exact step i j h
    · exact (step j i h).symm
    · exact wrap i j hi hj
    · exact (wrap j i hj hi).symm
  have hT (i : Fin (m+1)) : e i∈T := by
    refine Fin.cases hzT (fun j=>?_) i
    exact (hf.2.1 (commonPathOrder m hm j)).1
  have hF (i j : Fin (m+1)) : ¬F.Adj (e i) (e j) := by
    refine Fin.cases ?_ (fun a=>?_) i
    · refine Fin.cases (F.loopless.irrefl z) (fun b=>?_) j
      exact fun h=>hf.2.2.2.1 (commonPathOrder m hm b) z
        (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz) h.symm
    · refine Fin.cases ?_ (fun b=>?_) j
      · exact hf.2.2.2.1 (commonPathOrder m hm a) z
          (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz)
      · exact hf.2.2.1 (commonPathOrder m hm a) (commonPathOrder m hm b)
  obtain ⟨C,hC⟩ := ordinary_cycle_from_embedding Q F T (by omega) e hT hF hQ
  refine ⟨C,hC.trans ?_⟩
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨i,hi⟩
    cases i using Fin.cases with
    | zero => exact Or.inl hi.symm
    | succ j => exact Or.inr ⟨commonPathOrder m hm j,hi⟩
  · rintro (rfl|⟨j,hj⟩)
    · exact ⟨0,rfl⟩
    · obtain ⟨i,hi⟩ := commonPathOrder_surjective m hm j
      exact ⟨i.succ,by change f (commonPathOrder m hm i)=v;rw [hi];exact hj⟩

end Oberwolfach
