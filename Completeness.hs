module Completeness where

import Expression
import Deduction
import Data.List

getVariables :: Expression -> [String]
getVariables expr = nub (getVariables' expr)
    where getVariables' expr =
            case expr of
                Variable name -> [name]
                Negation a -> getVariables a
                Implication a b -> (getVariables a) ++ (getVariables b)
                Conjunction a b -> (getVariables a) ++ (getVariables b)
                Disjunction a b -> (getVariables a) ++ (getVariables b)

data VariableValue = VariableValue String Bool
    deriving(Show)

getVariableValue :: String -> [VariableValue] -> Bool
getVariableValue name [] = error "Empty variable list"
getVariableValue name (head : tail) =
   case head of
      VariableValue name' value -> if (name == name') then
         value
      else
         getVariableValue name tail

calculate :: Expression -> [VariableValue] -> Bool
calculate (Variable name) varlist = getVariableValue name varlist
calculate (Negation e) varlist = not $ calculate e varlist
calculate (Implication a b) varlist = (not $ calculate a varlist) || (calculate b varlist)
calculate (Conjunction a b) varlist = (calculate a varlist) && (calculate b varlist)
calculate (Disjunction a b) varlist = (calculate a varlist) || (calculate b varlist)

generateAllVariants :: [String] -> [[VariableValue]]
generateAllVariants [] = []
generateAllVariants [name] = [[VariableValue name True], [VariableValue name False]]
generateAllVariants (name:tail) =
    let tailVariants = generateAllVariants tail in
    (map (\ values -> (VariableValue name True):values) tailVariants) ++ (map (\ values -> (VariableValue name False):values) tailVariants)

proveVariantError = error "Unable to prove false statement"

proveVariant :: Expression -> [VariableValue] -> ProofTree

proveVariant x@(Variable name) varlist =
   if getVariableValue name varlist then
      Hypothesis x
   else
      proveVariantError

proveVariant x@(Negation (Variable name)) varlist =
   if not (getVariableValue name varlist) then
      Hypothesis x
   else
      proveVariantError

proveVariant (Implication a b) varlist =
   if calculate b varlist then
      ModusPonens (Hypothesis b) (axiom1 b a)
   else if not $ calculate a varlist then
      removeHypothesis a
      (ModusPonens
         (ModusPonens
            (truthImplication (Negation b) (Negation a))
            (ModusPonens
               (truthImplication (Negation b) a)
               (axiom9 (Negation b) a)
            )
         )
         (axiom10 b)
      )
   else
      proveVariantError

proveVariant (Negation (Implication a b)) varlist =
   if (calculate a varlist) && (not (calculate b varlist)) then
      ModusPonens
         (truthImplication (Implication a b) (Negation b))
         (ModusPonens
            (removeHypothesis (Implication a b) (ModusPonens (Hypothesis a) (Hypothesis (Implication a b))))
            (axiom9 (Implication a b) b)
         )
   else
      proveVariantError

-- Proves that (a -> b) -> (!b -> !a)
contraposition a b =
   removeHypothesis (Implication a b) $
   removeHypothesis (Negation b) $
   ModusPonens
      (truthImplication a (Negation b))
      (ModusPonens
         (Hypothesis (Implication a b))
         (axiom9 a b)
      )

-- Proves that (a | !a)
excludedMiddle a =
   ModusPonens
      (ModusPonens
         (ModusPonens
            (axiom7 a (Negation a))
            (contraposition (Negation a) (Disjunction a (Negation a)))
         )
         (ModusPonens
            (ModusPonens
               (axiom6 a (Negation a))
               (contraposition a (Disjunction a (Negation a)))
            )
            (axiom9 (Negation (Disjunction a (Negation a))) (Negation a))
         )
      )
      (axiom10 (Disjunction a (Negation a)))

processVariable :: Expression -> [VariableValue] -> [String] -> ProofTree
processVariable expr valueList [] = proveVariant expr valueList
processVariable expr valueList (var:varTail) =
   let proofOf b = processVariable expr (VariableValue var b : valueList) varTail in
   let proofTrue = proofOf True in
   let proofFalse = proofOf False in
   undefined

prove :: Expression -> ProofTree
prove expr = simplifyProof [] $ processVariable expr [] (getVariables expr)
