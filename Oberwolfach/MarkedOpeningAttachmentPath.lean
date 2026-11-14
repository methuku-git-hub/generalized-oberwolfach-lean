module

public import Oberwolfach.SeparatedDirectedPaths

@[expose] public section

/-! The path used when the marked arc is the prescribed outgoing arc:
its first endpoint has a marked spoke, all later path spokes are ordinary. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {V U : Type} [Fintype V] [DecidableEq V]

theorem marked_opening_attachment_path (F : SimpleGraph V)
    (R : V → V → Prop) (H₀ HK : V → U → Prop) (u : U)
    (W Z : Finset V) (l : ℕ) (hl : 1≤l) (a z : V)
    (haz : a≠z) (hazF : ¬F.Adj a z)
    (haW : a∉W) (hzW : z∉W) (haZ : a∉Z) (hzZ : z∉Z)
    (haF : ∀ x∈Z, ¬F.Adj a x) (hzF : ∀ x∈Z, ¬F.Adj z x)
    (haH : HK a u) (hzH : H₀ z u)
    (d c : ℝ) (hd : 0≤d) (hF : ∀ x, (F.degree x:ℝ)≤d)
    (hstep : ∀ x, c≤((Finset.univ.filter (fun y => R x y ∧ H₀ y u)).card:ℝ))
    (hjoin : ∀ x y, x≠y → c≤((Finset.univ.filter (fun q => R x q ∧ R q y ∧ H₀ q u)).card:ℝ))
    (hbudget : W.card+((Z.card:ℝ)+l+4)*(d+1)<c) :
    ∃ p : Fin (l+3) ↪ V, p 0=a ∧ p (Fin.last (l+2))=z ∧
      (∀ i : Fin (l+2), R (p i.castSucc) (p i.succ)) ∧
      HK (p 0) u ∧ (∀ i, i≠0 → H₀ (p i) u) ∧
      (∀ i, p i∉W ∧ p i∉Z ∧ ∀ x∈Z, ¬F.Adj (p i) x) ∧
      ∀ i j, ¬F.Adj (p i) (p j) := by
  let D : ℕ → V → V → Prop := fun _ => R
  let A : ℕ → Finset V := fun i => Finset.univ.filter (fun x => if i=0 then HK x u else H₀ x u)
  have hfirst : a∈A 0 := by simpa [A] using haH
  have hlast : z∈A (l+2) := by simpa [A] using hzH
  have hc : ∀ i<l, ∀ x∈A i, c≤(((A (i+1)).filter (D i x)).card:ℝ) := by
    intro i hi x hx
    have he : (A (i+1)).filter (D i x)=Finset.univ.filter (fun y => R x y ∧ H₀ y u) := by
      ext y; simp [A,D,and_comm]
    rw [he]; exact hstep x
  have hj : ∀ x∈A l, x≠z → c≤(((A (l+1)).filter (fun y => D l x y ∧ D (l+1) y z)).card:ℝ) := by
    intro x hx hxz
    have he : (A (l+1)).filter (fun y => D l x y ∧ D (l+1) y z)=
        Finset.univ.filter (fun y => R x y ∧ R y z ∧ H₀ y u) := by
      ext y; simp [A,D]; tauto
    rw [he]; exact hjoin x z hxz
  obtain ⟨p,hp0,hplast,hpA,hpD,hpF⟩ := separated_directed_path F D A W Z d c hd hF l a z
    haz hazF hfirst hlast haW hzW haZ hzZ haF hzF hc hj hbudget
  refine ⟨p,hp0,hplast,hpD,?_,?_,fun i => (hpA i).2,hpF⟩
  · rw [hp0]; exact haH
  · intro i hi
    have hv : i.val≠0 := fun h => hi (Fin.ext h)
    simpa only [A,Finset.mem_filter,Finset.mem_univ,true_and,if_neg hv] using (hpA i).1

end Oberwolfach
