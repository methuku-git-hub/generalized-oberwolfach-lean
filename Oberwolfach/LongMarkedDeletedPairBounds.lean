module

public import Oberwolfach.LongRawDeletedIncidence
public import Oberwolfach.TypedMarkedPairCosts

@[expose] public section
/-! The original marked seed family has the same near/far omitted-pair
bounds at every typed root and every deleted rim resource. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable
variable {n:ℕ} {U:Type} [Fintype U] [DecidableEq U] {m b:ℕ} {π:Equiv.Perm (Fin n)}

def longMarkedRootVertices : LongRawHubResource n U→Finset (Fin n)
  | Sum.inl e=>{Sum.elim Prod.fst Prod.fst e,Sum.elim Prod.snd Prod.snd e}
  | Sum.inr (_,v,_)=>{v}

theorem long_marked_deleted_rim_pair_near_far
    (hm:3≤m) (hn:0<n) (hu:Fintype.card U≤n)
    (w:MarkedWheel (Prod.fst:Fin n×Fin n→Fin n) Prod.snd Prod.fst Prod.snd m π b
      (fun _ (_:U)=>True) (fun _ (_:U)=>True)→ℝ) (B:ℝ) (hB:0≤B)
    (hw:∀W,0≤w W ∧ w W≤B/(n:ℝ)^m)
    (root:LongRawHubResource n U) (e:(Fin n×Fin n)⊕(Fin n×Fin n)):
    resourceOmittedPairWeight typedMarkedOccurrenceResources w root (Sum.inl e)≤
      if longRawResourceTail (U:=U) (Sum.inl e)∈longMarkedRootVertices root ∨
          longRawResourceHead (U:=U) (Sum.inl e)∈longMarkedRootVertices root then
        ((m:ℝ)+1)^4*B/(n:ℝ)
      else ((m:ℝ)+1)^4*B/(n:ℝ)^2 :=by
  cases root with
  | inl r =>
    have h:=typedMarkedPair_rim_rim hm (by simpa using hn) (by simpa using hu) w B hB
      (by simpa only [Fintype.card_fin] using hw) r e
    simp only [Fintype.card_fin] at h
    convert h using 1
    · congr 1
    · simp [longRawResourceTail,longRawResourceHead,longMarkedRootVertices]
  | inr r =>
    rcases r with ⟨mark,v,u⟩
    have h:=typedMarkedPair_spoke_rim hm (by simpa using hn) w B hB
      (by simpa only [Fintype.card_fin] using hw) e mark v u
    simp only [Fintype.card_fin] at h
    convert h using 1
    · congr 1
    · simp [longRawResourceTail,longRawResourceHead,longMarkedRootVertices]
end Oberwolfach
