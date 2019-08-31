universes u v

inductive imp (st : Type u)
| Seq : imp → imp → imp
| Modify : (st → st) → imp
| If : (st → Prop) → imp → imp → imp
| While : (st → Prop) → imp → imp

def Skip {α : Type u}: imp α := imp.Modify id

def repeat {α : Type u} (f : α → α) : α → ℕ → α
| v 0 := v
| v (nat.succ a) := repeat (f v) a

def imp_repeat {α : Type u} (f : imp α): ℕ → imp α := repeat (imp.Seq f) Skip

lemma repeat_succ {α : Type u} (f : α → α) (s : α) (n : ℕ):
   repeat f s (nat.succ n) = f (repeat f s n) :=
begin
unfold repeat,
induction n generalizing s,
trivial,
unfold repeat,
apply n_ih,
end