module

public import Oberwolfach.MarkedWheelResources

@[expose] public section

/-! Rotate a directed cycle immediately after its marked arc, retaining
all vertex labels, directions, edge types and the supplied permutation.
This connects explicitly constructed transformer paths to the manuscript's
canonical marked-cycle representation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 7000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

 def canonicalMarkedRotation {m:ℕ} (k:Fin (m+1)):Equiv.Perm (Fin (m+1)):=
  finCycle (finRotate (m+1) k)

 theorem canonicalMarkedRotation_zero {m:ℕ} (k:Fin (m+1)):
    canonicalMarkedRotation k 0=finRotate (m+1) k:=by
  simp [canonicalMarkedRotation,finCycle_apply]

 theorem canonicalMarkedRotation_last {m:ℕ} (k:Fin (m+1)):
    canonicalMarkedRotation k (Fin.last m)=k:=by
  have h:(Fin.last m:Fin (m+1))+1=0:=by rw [← finRotate_apply,finRotate_last]
  change (Fin.last m:Fin (m+1))+finRotate (m+1) k=k
  rw [finRotate_apply]
  calc
    _ = ((Fin.last m:Fin (m+1))+1)+k:=by abel
    _ = k:=by rw [h,zero_add]

 theorem canonicalMarkedRotation_rotate {m:ℕ} (k i:Fin (m+1)):
    canonicalMarkedRotation k (finRotate (m+1) i)=
      finRotate (m+1) (canonicalMarkedRotation k i):=by
  simp only [canonicalMarkedRotation,finCycle_apply,finRotate_apply]
  abel

 theorem canonicalMarkedRotation_ordinary {m:ℕ} (k:Fin (m+1)) (i:Fin m):
    canonicalMarkedRotation k i.castSucc≠k:=by
  intro h
  exact Fin.castSucc_ne_last i ((canonicalMarkedRotation k).injective (h.trans (canonicalMarkedRotation_last k).symm))

 theorem marked_cycle_from_cyclic_embedding {V E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (m:ℕ) (π:Equiv.Perm V) (b:ℕ)
    (z:Fin (m+1)↪V) (k:Fin (m+1))
    (hsep:PermutationSeparated π b z)
    (hO:∀ i,i≠k→∃ e,tail e=z i∧head e=z (finRotate (m+1) i))
    (hK:∃ e,ktail e=z k∧khead e=z (finRotate (m+1) k)):
    ∃ C:MarkedCycleTuple tail head ktail khead m π b,
      ∀ i,C.val i=z (canonicalMarkedRotation k i):=by
  let ρ:=canonicalMarkedRotation k
  let C:Fin (m+1)→V:=fun i=>z (ρ i)
  refine ⟨⟨C,?_,?_,?_⟩,fun _=>rfl⟩
  · intro i j hij
    exact hsep (ρ i) (ρ j) (fun h=>hij (ρ.injective h))
  · intro i
    obtain ⟨e,he₁,he₂⟩:=hO (ρ i.castSucc) (canonicalMarkedRotation_ordinary k i)
    refine ⟨e,he₁,?_⟩
    dsimp only [C]
    rw [he₂,← canonicalMarkedRotation_rotate k i.castSucc,finRotate_castSucc_eq_succ]
  · obtain ⟨e,he₁,he₂⟩:=hK
    refine ⟨e,?_,?_⟩
    · simpa only [C,ρ,canonicalMarkedRotation_last] using he₁
    · simpa only [C,ρ,canonicalMarkedRotation_zero] using he₂

 theorem marked_wheel_from_cyclic_embedding {V U E K:Type*}
    (tail head:E→V) (ktail khead:K→V) (m:ℕ) (π:Equiv.Perm V) (b:ℕ)
    (H₀ Hₖ:V→U→Prop) (z:Fin (m+1)↪V) (k:Fin (m+1)) (u:U)
    (hsep:PermutationSeparated π b z)
    (hO:∀ i,i≠k→∃ e,tail e=z i∧head e=z (finRotate (m+1) i))
    (hK:∃ e,ktail e=z k∧khead e=z (finRotate (m+1) k))
    (hspK:Hₖ (z (finRotate (m+1) k)) u)
    (hspO:∀ i,i≠finRotate (m+1) k→H₀ (z i) u):
    ∃ W:MarkedWheel tail head ktail khead m π b H₀ Hₖ,
      W.2.val=u∧∀ i,W.1.val i=z (canonicalMarkedRotation k i):=by
  obtain ⟨C,hC⟩:=marked_cycle_from_cyclic_embedding tail head ktail khead m π b z k hsep hO hK
  have hhub:MarkedHubCompatible H₀ Hₖ C.val u:=by
    constructor
    · simpa only [hC,canonicalMarkedRotation_zero] using hspK
    · intro i
      rw [hC]
      apply hspO
      rw [← canonicalMarkedRotation_zero k]
      exact fun h=>Fin.succ_ne_zero i ((canonicalMarkedRotation k).injective h)
  exact ⟨⟨C,⟨u,hhub⟩⟩,rfl,hC⟩

 theorem marked_cyclic_wheel_vertices {V U E K:Type*} [DecidableEq V]
    {tail head:E→V} {ktail khead:K→V} {m:ℕ} {π:Equiv.Perm V} {b:ℕ}
    {H₀ Hₖ:V→U→Prop} (z:Fin (m+1)↪V) (k:Fin (m+1))
    (W:MarkedWheel tail head ktail khead m π b H₀ Hₖ)
    (hW:∀ i,W.1.val i=z (canonicalMarkedRotation k i)):
    Finset.univ.image W.1.val=Finset.univ.image z:=by
  ext v
  simp only [Finset.mem_image,Finset.mem_univ,true_and,hW]
  constructor
  · rintro ⟨i,hi⟩;exact ⟨canonicalMarkedRotation k i,hi⟩
  · rintro ⟨i,hi⟩
    refine ⟨(canonicalMarkedRotation k).symm i,?_⟩
    simpa only [Equiv.apply_symm_apply] using hi

end Oberwolfach
