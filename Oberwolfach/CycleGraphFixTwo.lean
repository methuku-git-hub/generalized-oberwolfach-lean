module

public import Oberwolfach.CycleEdgeEnumeration

@[expose] public section
/-! An injective cycle-graph homomorphism fixing two consecutive vertices
fixes every vertex. This is used to count ordered representations. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem cycleGraph_injective_hom_fix_zero_one {r:ℕ} (hr:3≤r) (σ:Fin r→Fin r)
    (hinj:Function.Injective σ)
    (hmap:∀ i j,(SimpleGraph.cycleGraph r).Adj i j→(SimpleGraph.cycleGraph r).Adj (σ i) (σ j))
    (h0:σ ⟨0,by omega⟩=⟨0,by omega⟩) (h1:σ ⟨1,by omega⟩=⟨1,by omega⟩):∀ i,σ i=i:=by
  intro i
  induction hi:i.val using Nat.strong_induction_on generalizing i with
  | h n IH =>
    by_cases hz:n=0
    · have eq0:i=⟨0,by omega⟩:=Fin.ext (by simpa [hi] using hz)
      simpa [eq0] using h0
    by_cases ho:n=1
    · have eq1:i=⟨1,by omega⟩:=Fin.ext (by simpa [hi] using ho)
      simpa [eq1] using h1
    have hn:2≤n:=by omega
    let j:Fin r:=⟨n-1,by have:=i.isLt;omega⟩
    let p:Fin r:=⟨n-2,by have:=i.isLt;omega⟩
    have hj:σ j=j:=IH (n-1) (by omega) j rfl
    have hp:σ p=p:=IH (n-2) (by omega) p rfl
    have hjnext:j.val+1<r:=by dsimp [j];have:=i.isLt;omega
    have hsource:(SimpleGraph.cycleGraph r).Adj j i:=by
      rw [cycleGraph_modular_adj (by omega)]
      left
      rw [Nat.mod_eq_of_lt hjnext]
      dsimp [j]
      omega
    have htarget:=hmap j i hsource
    rw [hj,cycleGraph_modular_adj (by omega)] at htarget
    rcases htarget with hfor|hback
    · apply Fin.ext
      rw [Nat.mod_eq_of_lt hjnext] at hfor
      dsimp [j] at hfor
      omega
    · have hlt:(σ i).val+1<r:=by
        by_contra hnot
        have hEq:(σ i).val+1=r:=by have:=(σ i).isLt;omega
        rw [hEq,Nat.mod_self] at hback
        dsimp [j] at hback
        omega
      rw [Nat.mod_eq_of_lt hlt] at hback
      have he:σ i=σ p:=by
        rw [hp]
        apply Fin.ext
        dsimp [j,p] at *
        omega
      have :=hinj he
      have hv:=congrArg Fin.val this
      dsimp [p] at hv
      omega
end Oberwolfach
