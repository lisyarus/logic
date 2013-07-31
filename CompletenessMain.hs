module Main where

import Expression
import Completeness

do_main :: String -> String
do_main str =
    let expression = parse str
        variables = getVariables expression in
    if foldl (&&) True $ map (calculate expression) (generateAllVariants variables) then
        "Need a proof of this..."
    else
        error "The formula is not logically valid!"

main = interact ((\l -> l ++ "\n") . do_main . head . lines)
