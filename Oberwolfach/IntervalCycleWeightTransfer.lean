module

public import Oberwolfach.ThreeIntervalCycleRepresentation

@[expose] public section

/-! Transfer exact capacity equations through the proved cycle/path bijection. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

def cycleWeightsOfIntervals {X : Type*} (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (ω : (∀ i,Fin (L i+1) → X) → ℝ) (v : Fin (∑ i,L i) → X) : ℝ :=
  ω (threePathsOfCycle L hL v)

theorem cycleWeightsOfIntervals_total {X : Type*} [Fintype X]
    (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (ω : (∀ i,Fin (L i+1) → X) → ℝ)
    (hω : ∀ p,0≤ω p)
    (hsupp : ∀ p,0<ω p → ∀ i,p i (Fin.last (L i))=p (finRotate 3 i) 0) :
    (∑ v,cycleWeightsOfIntervals L hL ω v)=∑ p,ω p := by
  exact threePathsOfCycle_sum L hL ω
    (fun p hp => hsupp p (lt_of_le_of_ne (hω p) (Ne.symm hp)))

theorem cycleWeightsOfIntervals_edge {X : Type*} [Fintype X]
    (L : Fin 3 → ℕ) (hL : ∀ i,0<L i)
    (ω : (∀ i,Fin (L i+1) → X) → ℝ)
    (hω : ∀ p,0≤ω p)
    (hsupp : ∀ p,0<ω p → ∀ i,p i (Fin.last (L i))=p (finRotate 3 i) 0)
    (a : Fin (∑ i,L i) → X → X → ℝ)
    (hedge : ∀ (i : Fin 3) (j : Fin (L i)) (x y : X),
      (∑ p,if p i j.castSucc=x ∧ p i j.succ=y then ω p else 0)=a (finSigmaFinEquiv ⟨i,j⟩) x y)
    (k : Fin (∑ i,L i)) (x y : X) :
    (∑ v,if v k=x ∧ v (finRotate (∑ i,L i) k)=y then cycleWeightsOfIntervals L hL ω v else 0)=a k x y := by
  let q : Σ i,Fin (L i) := finSigmaFinEquiv.symm k
  have hq : finSigmaFinEquiv q=k := Equiv.apply_symm_apply _ _
  let f (p : ∀ i,Fin (L i+1) → X) := if p q.1 q.2.castSucc=x ∧ p q.1 q.2.succ=y then ω p else 0
  have hf : ∀ p,f p≠0 → ∀ i,p i (Fin.last (L i))=p (finRotate 3 i) 0 := by
    intro p hp
    have hz : ω p≠0 := by intro hz;simp [f,hz] at hp
    exact hsupp p (lt_of_le_of_ne (hω p) (Ne.symm hz))
  have hh := threePathsOfCycle_sum L hL f hf
  have heval (v : Fin (∑ i,L i) → X) :
      f (threePathsOfCycle L hL v)=
        if v k=x ∧ v (finRotate (∑ i,L i) k)=y then cycleWeightsOfIntervals L hL ω v else 0 := by
    have hb := threePathsOfCycle_edge L hL v q.1 q.2
    simp only [f,hb.1,hb.2,hq,cycleWeightsOfIntervals]
  simp only [heval] at hh
  rw [show (∑ p,f p)=a k x y by simpa only [hq] using hedge q.1 q.2 x y] at hh
  exact hh

theorem cycleWeight_zero_at_zero_capacity {c : ℕ} {X : Type*} [Fintype X]
    (a : Fin c → X → X → ℝ) (w : (Fin c → X) → ℝ) (hw : ∀ v,0≤w v)
    (he : ∀ i x y,(∑ v,if v i=x ∧ v (finRotate c i)=y then w v else 0)=a i x y)
    (v : Fin c → X) (i : Fin c) (hz : a i (v i) (v (finRotate c i))=0) : w v=0 := by
  have hh := Finset.single_le_sum
    (s := Finset.univ) (f := fun q : Fin c → X => if q i=v i ∧ q (finRotate c i)=v (finRotate c i) then w q else 0)
    (fun q _ => by split_ifs;exact hw q;exact le_rfl) (Finset.mem_univ v)
  simp only [and_self,ite_true,he,hz] at hh
  exact le_antisymm hh (hw v)

end Oberwolfach
