module Main where

import Expression
import Deduction


a = Variable "A"
b = Variable "B"

p = Proof [Conjunction a b] (ModusPonens
    (ModusPonens
        (Hypothesis (Conjunction a b))
        (Axiom (Implication (Conjunction a b) a))
    )
    (ModusPonens
        (ModusPonens
            (Hypothesis (Conjunction a b))
            (Axiom (Implication (Conjunction a b) b))
        )
        (Axiom (Implication b (Implication a (Conjunction b a))))
    ))

main = print (deduction p)
