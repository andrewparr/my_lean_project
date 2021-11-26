import tactic

-- lets work in a namespace to avoid changing anything in mathlib
namespace british_natural_numbers

-- In Britain Natural numbers start with 1
inductive bnat
| one             : bnat
| succ (n : bnat) : bnat

-- defining addition on bnat
def add : bnat → bnat → bnat
| n bnat.one   := bnat.succ n              -- adding one to any number is just the successor of that number
| n (bnat.succ(d)) := bnat.succ(add n d)   -- adding n with succ(d) is defined as succ (n + d)

-- I don't want to type bnat all the time
open bnat

def two   := succ(one)
def three := succ(two)
def four  := succ(three)

lemma test : add two two = four :=
begin
  -- goal is add two two = four
  -- lets unfold two as succ one
  unfold two at *,
  -- we now have add one.succ one.succ so rw add
  rw add,
  rw add,
  -- goal is now one.succ.succ.succ = four
  -- so lets unfold definition of four
  unfold four,
  unfold three,
  unfold two,
  -- here the proof is complete, because unfold two automatically does refl
  -- if it didn't our goal would have been.
  -- one.succ.succ.succ = one.succ.succ.succ
  -- which is closed by reflexivity
end

-- What about zero ?


end british_natural_numbers
