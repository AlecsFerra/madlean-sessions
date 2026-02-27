/-
Elaboration and Kernel
25-02-2026, Faculty of Mathematics of UCM
Juanjo Madrigal
-/

-- # Implicit arguments

def id1 (a : α) : α := a
#check id1 5
#check id1

def id2 (α : Type) (a : α) : α := a
#check id2 Nat 5

def id3 {α : Type} (a : α) : α := a
#check id3 5
#eval @id3 Nat 5

def id4 {α β : Type} (a : α) : α := a
#check id4 5

def id5 {α β : Type} (a : α) : List β := []
#check id5 5


-- # Typeclasses

def double {α : Type} [Add α] (x : α) : α :=
  x + x

#check double 10
#check double 3.14


-- # Tactics

theorem t1 : 3 = 3 := by simp
#print t1
#check @eq_self

theorem t2 : p -> q -> (p ∧ q) := by
  intro hp hq
  apply And.intro
  · exact hp
  · exact hq

#print t2


-- # Inductive types

-- Natural numbers

inductive Nt where
  | Z : Nt
  | S : Nt -> Nt

def f1 : Nt -> String
| .Z => "Foo"
| .S n => f1 n ++ "!"

#eval f1 <| Nt.S (Nt.S Nt.Z)

#print f1

set_option pp.notation false

#print f1

#print Nt.Z
#print Nt.S
#print Nt.rec
#print Nt.brecOn
#print Nt.brecOn.go
#print Nt.casesOn
#print Nt.ctorIdx

#print Nat.zero
#print Nat.succ
#print Nat.rec

def g1 : Nat -> String
| 0     => "Foo"
| n + 1 => g1 n ++ "!"

#print g1
#print g1.match_1

def g2 : Nat -> Nat
| 0     => 5
| n + 1 => n

#print g2

def g3 : Nat -> String
| 0 => "Zero"
| 1 => "One"
| 2 => "Two"
| 3 => "Three"
| 4 => "Four"
| _ => "A lot"

#print g3
#print g3.match_1


-- Simple binary type

inductive Bin where
  | A : Bin
  | B : Bin

#print Bin.A
#print Bin.B
#print Bin.rec
#print Bin.ctorIdx

def nb : Bin.A ≠ Bin.B := by simp
#print nb

inductive BinP : Prop where
  | A : BinP
  | B : BinP

#print BinP.A
#print BinP.B
#print BinP.rec
-- #print BinP.ctorIdx

-- def nbp : BinP.A ≠ BinP.B := by simp

-- what is the relation between Lean and Axiom K?
inductive Eqq : x -> x -> Type 11 where
| rrefl : Eqq x x

def uip : (p : Eqq a b) -> (q : Eqq a b) -> (Eqq p q)
| .rrefl, .rrefl => .rrefl

#print uip
#print axioms uip
#print Eqq.rec
