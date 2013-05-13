module Main where

import Expression
import Deduction


a = Variable "A"
b = Variable "B"
ax1 = Conjunction a b
ax2 = Implication ax1 a

p = Proof [ax1, ax2] (ModusPonens (Hypothesis ax1) (Hypothesis ax2))

main = print p
