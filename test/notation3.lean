import Std.Tactic.GuardMsgs
import Mathlib.Mathport.Notation
import Mathlib.Init.Data.Nat.Lemmas

set_option pp.unicode.fun true
set_option autoImplicit true

namespace Test

-- set_option trace.notation3 true

def Filter (α : Type) : Type := (α → Prop) → Prop
def Filter.atTop [Preorder α] : Filter α := fun _ => True
def Filter.eventually (p : α → Prop) (f : Filter α) := f p
def Filter.top (α : Type) : Filter α := fun s => ∀ x, s x

notation3 "∀ᶠ " (...) " in " f ", " r:(scoped p => Filter.eventually p f) => r

/-- info: ∀ᶠ (x : ℕ) (y : ℕ) in Filter.atTop, x < y : Prop -/
#guard_msgs in #check ∀ᶠ (x : Nat) (y) in Filter.atTop, x < y
/-- info: ∀ᶠ (x : ℕ) in Filter.atTop, x < 3 : Prop -/
#guard_msgs in #check ∀ᶠ x in Filter.atTop, x < 3

section
open Mathlib.FlexibleBinders Lean

macro_rules
  | `(binderDefault%(finset, $e)) => `(binderResolved%(Filter.top, $e))

/-- For the `filter` domain, `(x : ty)` is a binder over `Filter.top` for `ty`. -/
macro_rules
  | `(binder%(filter, ($e :%$c $ty))) => do
    if e matches `($_ $_*) then Macro.throwUnsupported
    if e matches `(($_ : $_)) then Macro.throwErrorAt c "Unexpected type ascription"
    `(binderResolved%((Filter.top : Filter $ty), $e))

macro_rules
  | `(binder%(filter, $e ∈ $f)) => do
    let (e, ty) ← destructAscription e
    if e matches `($_ $_*) then Macro.throwUnsupported
    `(binderResolved%(($f : Filter $ty), $e))

end

--notation3 "∀ᶠ' " (...) ", " r:(scoped (filter) p => Filter.eventually p f) => r

def foobar (p : α → Prop) (f : Prop) := ∀ x, p x = f

notation3 "∀ᶠᶠ " (...) " in " f ": "
  r1:(scoped p => Filter.eventually p f) ", " r2:(scoped p => foobar p r1) => r2

/-- info: ∀ᶠᶠ (x : ℕ) (y : ℕ) in Filter.atTop: x < y, x = y : Prop -/
#guard_msgs in #check ∀ᶠᶠ (x : Nat) (y) in Filter.atTop: x < y, x = y
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check ∀ᶠᶠ x in Filter.atTop: x < 3, x = 1
/-- info: ∀ᶠᶠ (x : ℕ) in Filter.atTop: x < 3, x = 1 : Prop -/
#guard_msgs in #check foobar (fun x ↦ Eq x 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)
/-- info: foobar (fun y ↦ y = 1) (∀ᶠ (x : ℕ) in Filter.atTop, x < 3) : Prop -/
#guard_msgs in #check foobar (fun y ↦ Eq y 1) (Filter.atTop.eventually fun x ↦ LT.lt x 3)

notation3 "∃' " (...) ", " r:(scoped p => Exists p) => r
/-- info: ∃' (x : ℕ) (_ : x < 3), x < 3 : Prop -/
#guard_msgs in #check ∃' x < 3, x < 3

def func (x : α) : α := x
notation3 "func! " (...) ", " r:(scoped p => func p) => r
-- Make sure it handles additional arguments. Should not consume `(· * 2)`.
-- Note: right now this causes the notation to not pretty print at all.
/-- info: func (fun x ↦ x) fun x ↦ x * 2 : ℕ → ℕ -/
#guard_msgs in #check (func! (x : Nat → Nat), x) (· * 2)

structure MyUnit where
notation3 "~{" (x"; "* => foldl (a b => Prod.mk a b) MyUnit) "}~" => x
/-- info: ~{1; true; ~{2}~}~ : ((Type × ℕ) × Bool) × Type × ℕ -/
#guard_msgs in #check ~{1; true; ~{2}~}~
/-- info: ~{}~ : Type -/
#guard_msgs in #check ~{}~

notation3 "%[" (x", "* => foldr (a b => List.cons a b) List.nil) "]" => x
/-- info: %[1, 2, 3] : List ℕ -/
#guard_msgs in #check %[1, 2, 3]

def foo (a : Nat) (f : Nat → Nat) := a + f a
def bar (a b : Nat) := a * b
notation3 "*[" x "] " (...) ", " v:(scoped c => bar x (foo x c)) => v
/-- info: *[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *[1] (x) (y), x + y
/-- info: bar 1 : ℕ → ℕ -/
#guard_msgs in #check bar 1

-- Checking that the `<|` macro is expanded when making matcher
def foo' (a : Nat) (f : Nat → Nat) := a + f a
def bar' (a b : Nat) := a * b
notation3 "*'[" x "] " (...) ", " v:(scoped c => bar' x <| foo' x c) => v
/-- info: *'[1] (x : ℕ) (y : ℕ), x + y : ℕ -/
#guard_msgs in #check *'[1] (x) (y), x + y
/-- info: bar' 1 : ℕ → ℕ -/
#guard_msgs in #check bar' 1

-- Currently does not pretty print due to pi type
notation3 (prettyPrint := false) "MyPi " (...) ", " r:(scoped p => (x : _) → p x) => r
/-- info: ∀ (x : ℕ), (fun x ↦ ∀ (x_1 : ℕ), (fun y ↦ x < y) x_1) x : Prop -/
#guard_msgs in #check MyPi (x : Nat) (y : Nat), x < y

-- The notation parses fine, but the delaborator never succeeds, which is expected
def myId (x : α) := x
notation3 "BAD " c "; " (x", "* => foldl (a b => b) c) " DAB" => myId x
/-- info: myId 3 : ℕ -/
#guard_msgs in #check BAD 1; 2, 3 DAB

inductive ExistsF {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : ExistsF p

notation3 "∃F " (...) ", " r:(scoped p => Exists p, p r => p ∧ r) => r

/-- info: ∃F (x : ℕ), x = x : Prop -/
#guard_msgs in #check ∃F (x : Nat), x = x
/-- info: ∃F (x : ℕ) (y : ℕ), y < x ∧ x = y : Prop -/
#guard_msgs in #check ∃F (x : Nat) (y < x), x = y
/-- info: ∃F (x : ℕ), x < 10 ∧ ∃F (y : ℕ), y < 10 ∧ x + y = 1 : Prop -/
#guard_msgs in #check ∃F x y < 10, x + y = 1
