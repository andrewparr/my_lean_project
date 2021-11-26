-- Based on Kevin Buzzard's Zulip message "Two hours of Lean" - Nov 23rd 2021

import tactic

-- Define a number as a zero, and a successor
inductive number
| zero           : number
| S (n : number) : number

-- start a namespace to work in (means we can type zero rather than number.zero)
namespace number

-- Define some common numbers
def one   := S(zero)
def two   := S(one)
def three := S(two)
def four  := S(three)

-- before we can prove two + two = four we have to define what + means

-- add is a binary operator on two numbers that make another number
def add : number → number → number
| n zero   := n            -- adding zero to a number just returns that number
| n (S(d)) := S(add n d)   -- adding a non zero number to n is the successor of n and that non zero number

-- Surprisingly refl will easily prove this
example : add two two = four := rfl

-- We can't at this point write 2 + 2 because we haven't defined the infix notation of +

-- In lean we define the infix notation + to be number.add
infix `+` := number.add

-- and now we can write
example : two + two = four := rfl

-- end our namespace
end number
