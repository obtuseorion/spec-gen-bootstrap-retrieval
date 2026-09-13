import Aeneas
/-!
# Helpers referenced by mutants (Task 4)

Semantic-relation mutants on list/array-valued results and the `drop_bind`
operator are expressed through these functions so that a mutant stays a
well-typed program: `ok e` becomes `ok (LeanTools.Mut.perm e)` and so on, and
a mutant only elaborates when the instance exists for `e`'s type.
-/
open Aeneas Aeneas.Std

namespace LeanTools.Mut

/-- Types that behave like a sequence for the purpose of semantic mutants. -/
class SeqLike (α : Type u) where
  /-- a permutation of the sequence (its reverse) -/
  perm : α → α
  /-- one element duplicated -/
  dup : α → α
  /-- one element dropped (rotated, for fixed-length arrays) -/
  drop : α → α

instance : SeqLike (List α) where
  perm l := l.reverse
  dup l := l ++ l.take 1
  drop l := l.tail

instance {n : Usize} : SeqLike (Array α n) where
  perm a := ⟨a.val.reverse, by simp [a.property]⟩
  dup a := match h : a.val with
    | x :: _ :: rest => ⟨x :: x :: rest, by
        have hp := a.property; rw [h] at hp; simpa using hp⟩
    | _ => a
  drop a := ⟨a.val.tail ++ a.val.take 1, by
    have := a.property
    rcases h : a.val with _ | ⟨x, l⟩ <;> simp_all⟩

instance : SeqLike (Slice α) where
  perm s := ⟨s.val.reverse, by simp [s.property]⟩
  dup s := if h : (s.val ++ s.val.take 1).length ≤ Usize.max then ⟨_, h⟩ else s
  drop s := ⟨s.val.tail, by have := s.property; simp; omega⟩

instance : SeqLike (alloc.vec.Vec α) where
  perm v := ⟨v.val.reverse, by simp [v.property]⟩
  dup v := if h : (v.val ++ v.val.take 1).length ≤ Usize.max then ⟨_, h⟩ else v
  drop v := ⟨v.val.tail, by have := v.property; simp; omega⟩

def perm [SeqLike α] (x : α) : α := SeqLike.perm x
def dup [SeqLike α] (x : α) : α := SeqLike.dup x
def drop [SeqLike α] (x : α) : α := SeqLike.drop x

/-- `let x ← e; k` ↦ `let x ← dropBind e; k`: the bound value becomes `default`
and `e`'s failure no longer propagates. `e` is used only for its type. -/
def dropBind {α : Type u} [Inhabited α] (_e : Result α) : Result α := Result.ok default

end LeanTools.Mut
