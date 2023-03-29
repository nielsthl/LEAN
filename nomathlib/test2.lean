def main :

namespace hides

inductive nat : Type
| zero : nat
| succ : nat → nat

def nat_to_string : nat → string
| nat.zero := "0"
| (nat.succ n) := "succ(" ++ nat_to_string n ++ ")"

instance : has_repr nat := ⟨nat_to_string⟩

def add : nat → nat → nat
| m nat.zero := m
| m (nat.succ n) := nat.succ (add m n)

def zero : nat := nat.zero
def one : nat := nat.succ nat.zero
def two : nat := nat.succ one
def three : nat := nat.succ two

#eval three

end hides

def even (n : nat) : Prop := ∃ m, n = 2 * m
def odd (n : nat) : Prop := ∃ m, n = 2 * m + 1

#check ∀ n, even n ∨ even (n+1)

lemma even_10: even 10 :=
begin
  use 5,
  refl,
end

theorem even_plus_even {n m : nat} (h1 : even n) (h2 : even m) : even (n + m) :=
begin
  cases h1 with k hk,
  cases h2 with l hl,
  use k + l,
  rw [hk, hl],
  ring,
end

inductive mynat : Type
| zero : mynat
| succ : mynat → mynat


variables (p q : Prop)

theorem and_comm : p ∧ q → q ∧ p :=
begin
  assume h,
  cases h with hp hq,
  split,
  exact hq,
  exact hp,
end

theorem and_left : p ∧ q → p :=
begin
  assume h,
  cases h with hp hq,
  exact hp,
end

theorem or_left : p ∨ q → p :=
begin
  assume h,
  cases h with hp hq,
 exact hp,
end 