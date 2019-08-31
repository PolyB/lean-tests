import init.function
import .imp
import tactic.find

universes u v
local attribute [instance] classical.prop_decidable


inductive big_step {st : Type u}: st → imp st → st → Prop
| Seq : ∀ s₁ s₂ s₃ i₁ i₂, big_step s₁ i₁ s₂ → big_step s₂ i₂ s₃ → big_step s₁ (imp.Seq i₁ i₂) s₃
| Modify : ∀s f, big_step s (imp.Modify f) (f s)
| IfTrue : ∀ s₁ s₂ (c : st → Prop) i₁ i₂ , c s₁ →  big_step s₁ i₁ s₂ → big_step s₁ (imp.If c i₁ i₂) s₂
| IfFalse : ∀ s₁ s₂ (c : st → Prop) i₁ i₂, ¬ c s₁  → big_step s₁ i₂ s₂ → big_step s₁ (imp.If c i₁ i₂) s₂
| WhileTrue : ∀ s₁ s₂ (c : st → Prop) i, c s₁ →  big_step s₁ (imp.Seq i (imp.While c i)) s₂ → big_step s₁ (imp.While c i) s₂
| WhileFalse : ∀ s (c : st → Prop) i, ¬ c s → big_step s (imp.While c i) s

local notation a `≃` b := ∀ s₁ s₂, big_step s₁ a s₂ ↔ big_step s₁ b s₂



lemma imp_repeat_succ {α : Type u} {i : imp α} {n : ℕ} : 
   (imp_repeat i (nat.succ n)) ≃ (imp.Seq i (imp_repeat i n)) :=
begin
intros,
split,
intros,
unfold imp_repeat at a,
rw repeat_succ at a,
cases a,
constructor,
apply a_a,
unfold imp_repeat,
assumption,
intros,
unfold imp_repeat,
rw repeat_succ,
cases a,
constructor,
assumption,
assumption,
end

lemma imp_seq_skip {α : Type u} { i : imp α} {s₁ s₂ : α}:
   big_step s₁ (imp.Seq Skip i) s₂ ↔ big_step s₁ i s₂ :=
begin
split,
intros,
cases a,
cases a_a,
assumption,
intros,
constructor,
constructor,
assumption,
end

lemma imp_under_seq1 {α : Type u} { i₁ i' i₂ : imp α} :
   (i₁ ≃ i') → ((imp.Seq i₁ i₂) ≃ (imp.Seq i' i₂)) :=
begin
intros,
split,
intros,
cases a_1,
constructor,
rw a at a_1_a,
assumption,
assumption,
intros,
cases a_1,
constructor,
rw <-a at a_1_a,
assumption,
assumption,
end

lemma seq_inv {α : Type u} { i₁ i₂ i₃ : imp α} :
   (imp.Seq (imp.Seq i₁ i₂) i₃) ≃ (imp.Seq i₁ (imp.Seq i₂ i₃)) :=
begin
intros,
split,
intros,
cases a,
cases a_a,
constructor,
assumption,
constructor,
assumption,
assumption,
intros,
cases a,
cases a_a_1,
constructor,
constructor,
assumption,
assumption,
assumption,
end

lemma while_is_repeat {α : Type u} {c : α → Prop} { i : imp α} {s₁ s₂ : α} {n : ℕ} {w : ∀x s, x ≤ n →  big_step s₁ (imp_repeat i x) s → c s}:
   (big_step s₁ (imp.While c i) s₂) → big_step s₁ (imp.Seq (imp_repeat i n) (imp.While c i)) s₂ :=
   begin
induction n generalizing s₁,
case nat.zero {
   intros,
   unfold imp_repeat repeat,
   constructor,
   constructor,
   assumption,
},
case nat.succ {
   intros,
   rw (imp_under_seq1 imp_repeat_succ),
   rw seq_inv,
   cases a,
   case big_step.WhileTrue {
      cases a_a_1,
      constructor,
      assumption,
      apply n_ih,
      assumption,
      intros,
      apply w (nat.succ x),
      apply nat.succ_le_succ,
      assumption,
      rw imp_repeat_succ,
      constructor,
      assumption,
      assumption,
   },
   case big_step.WhileFalse {
      exfalso,
      apply a_a,
      apply w,
      apply nat.zero_le,
      unfold imp_repeat repeat,
      constructor,
   },
},
end

lemma while_is_seq  {α : Type u} {c : α → Prop} {i : imp α} {s₁ s₂ : α} {w : c s₁}:
   big_step s₁ (imp.While c i) s₂ ↔ big_step s₁ (imp.Seq i (imp.While c i)) s₂ :=
begin
split,
{
   intros,
   cases a,
   case big_step.WhileTrue {
      assumption,
   },
   case big_step.WhileFalse {
      contradiction,
   },
},
{
   intros,
   apply big_step.WhileTrue,
   assumption,
   assumption,
}
end

lemma while_equiv_repeat {α : Type u} {c : α → Prop} { i : imp α} {s₁ s₂ : α} (n : ℕ)
                        {w : ∀x s, x < n →  big_step s₁ (imp_repeat i x) s → c s} 
                        {wf : ∀ s, big_step s₁ (imp_repeat i n) s → ¬ c s}:
      big_step s₁ (imp.While c i) s₂  ↔  big_step s₁ (imp_repeat i n) s₂ :=
begin
intros,
induction n generalizing s₁,
case nat.zero {
   intros,
   unfold imp_repeat repeat,
   split,
   intros,
   cases a,
   case big_step.WhileTrue {

      exfalso,
      apply wf,
      constructor,
      simp,
      assumption
   },
   case big_step.WhileFalse {
      constructor,
   },

   intros,
   cases a,
   apply big_step.WhileFalse,
   apply wf,
   constructor,
},
case nat.succ {
   split,
   intros,
   rw imp_repeat_succ,
   cases a,
   case big_step.WhileTrue {
      cases a_a_1,
      constructor,
      assumption,
      rw <-n_ih,
      assumption,
      intros,
      apply w,
      apply (nat.succ_lt_succ a),
      rw imp_repeat_succ,
      constructor,
      assumption,
      assumption,
      intros,
      apply wf,
      rw imp_repeat_succ,
      constructor,
      assumption,
      assumption,
   },
   case big_step.WhileFalse {
      exfalso,
      apply a_a,
      apply w,
      apply nat.zero_lt_succ,
      constructor,
   },

   intros,



   rw imp_repeat_succ at a,
   cases a,
   have u : big_step a_s₂ (imp_repeat i n_n) s₂ := a_a_1,
   rw <-n_ih at u,
   rw while_is_seq,
   constructor,
   assumption,
   assumption,

   apply w,
   apply nat.zero_lt_succ,
   constructor,
   intros,
   apply w,
   apply nat.succ_lt_succ a,
   rw imp_repeat_succ,
   constructor,
   assumption,
   assumption,
   intros,
   apply wf,
   rw imp_repeat_succ,
   constructor,
   assumption,
   assumption,

},
end

def tr {α : Type u} {β : Type v} (tr_from : (α → β)) (tr_to : (β → α)) : imp α → imp β
| (imp.Seq i₁ i₂) := (imp.Seq (tr i₁) (tr i₂))
| (imp.Modify m) := (imp.Modify (tr_from ∘ m ∘ tr_to))
| (imp.If c t f) := (imp.If (c ∘ tr_to) (tr t) (tr f))
| (imp.While c t) := (imp.While (c ∘ tr_to) (tr t))

lemma case_imp_modify {α : Type u} {s₁ s₂ : α} {f} : big_step s₁ (imp.Modify f) s₂ ↔ s₂ = f s₁  := 
begin
split,
intros,
cases a,
trivial,
intros,
rw a,
constructor,
end

lemma case_while {α : Type u} {s₁ s₂ : α} {c} {i} (w:big_step s₁ (imp.While c i) s₂): 
   (c s₁ ∧ big_step s₁ (imp.Seq i (imp.While c i)) s₂) ∨ (¬ c s₁ ∧ s₁ = s₂) :=
begin
intros,
cases w,
left,
split,
assumption,
assumption,
right,
split,
assumption,
trivial,
end

def is_inverse {α : Type u} { β : Type v} (f : α → β) (g : β → α) :=
   (∀ x, f (g x) = x) ∧ (∀ y, g (f y) = y)

lemma inverse_is_bij {α : Type u} {β : Type v} {f : α → β } {g : β → α} (i : is_inverse f g):
   function.bijective f :=
begin
unfold is_inverse at i,
cases i,
unfold function.bijective,
split,
{
unfold function.injective,
intros,
rw <-(i_right a₁), 
rw <-(i_right a₂),
rw a,
},
{
unfold function.surjective,
intros,
existsi (g b),
rw i_left,
},
end

lemma is_inverse_rev {α : Type u} {β : Type v} {f : α → β } {g : β → α} (w : is_inverse f g) :
   is_inverse g f :=
begin
destruct w,
intros,
constructor,
intros,
apply right,
apply left,
end

lemma while_inv {α : Type u} {s₁ s₂ : α} {c : α → Prop} {i : imp α} (a : big_step s₁ (imp.While c i) s₂) (P :Prop) :
   ((c s₁ ∧ big_step s₁ (imp.Seq i (imp.While c i)) s₂) → P)
   → ((¬ c s₁ ∧ big_step s₁ (imp.While c i) s₁) → P)
   → P :=
begin
intros,
cases a,
apply a_1,
split,
assumption,assumption,
apply a_2,
split,
assumption,assumption,
end