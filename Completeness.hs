module Completeness where

import Expression
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

getVariableValue name varlist =
    case head varlist of
        VariableValue name' val -> if name == name' then val else getVariableValue name (tail varlist)

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
