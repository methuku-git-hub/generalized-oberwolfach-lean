module

public import Oberwolfach.SimpleWalkIntervalConcatenation

@[expose] public section
/-! Appending two directed walks preserves their directed successor relation. -/
set_option autoImplicit false
noncomputable section
namespace Oberwolfach
attribute [local instance] Classical.propDecidable

theorem walk_append_preserves_successor_relation
    {V:Type*} {G:SimpleGraph V} {a b c:V} (p:G.Walk a b) (q:G.Walk b c) (R:V→V→Prop)
    (hp:∀k,k<p.length→R (p.getVert k) (p.getVert (k+1)))
    (hq:∀k,k<q.length→R (q.getVert k) (q.getVert (k+1))):
    ∀k,k<(p.append q).length→R ((p.append q).getVert k) ((p.append q).getVert (k+1)):=by
  intro k hk
  rw [SimpleGraph.Walk.length_append] at hk
  by_cases h:k<p.length
  · rw [SimpleGraph.Walk.getVert_append' p q k,SimpleGraph.Walk.getVert_append' p q (k+1)]
    simp only [if_pos (show k≤p.length by omega),if_pos (show k+1≤p.length by omega)]
    exact hp k h
  · have hle:p.length≤k:=by omega
    rw [SimpleGraph.Walk.getVert_append p q k,SimpleGraph.Walk.getVert_append p q (k+1)]
    simp only [if_neg (show ¬k<p.length by omega),if_neg (show ¬k+1<p.length by omega)]
    have he:k+1-p.length=(k-p.length)+1:=by omega
    rw [he]
    exact hq (k-p.length) (by omega)
end Oberwolfach
