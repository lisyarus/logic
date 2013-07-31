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

data ProofHeader = ProofHeader [Expression] Expression
    deriving(Show)

data ProofHeaderParseState = ProofHeaderParseState [Expression] TokenList

parseProofHypo :: TokenList -> ProofHeaderParseState
parseProofHypo tokenList =
    case parseImplication tokenList of
        ParseState expr (":-":tail) -> ProofHeaderParseState [expr] tail
        ParseState expr (",":tail) ->
            case parseProofHypo tail of
                ProofHeaderParseState hypoList tail -> ProofHeaderParseState (expr:hypoList) tail

parseProofHeader :: TokenList -> ProofHeader
parseProofHeader tokenList =
    case tokenList of
        ":-":tail -> ProofHeader [] (stateExpression $ parseImplication tail)
        _ -> case parseProofHypo tokenList of
            ProofHeaderParseState hypoList tail -> ProofHeader hypoList (stateExpression $ parseImplication tail)

findProof :: Expression -> [ProofTree] -> Maybe ProofTree
findProof expr [] = Nothing
findProof expr proofList =
    if (proofStatement $ head proofList) == expr then
        Just (head proofList)
    else
        findProof expr (tail proofList)

findModusPonens :: Expression -> [ProofTree] -> ProofTree
findModusPonens expr [] = error ("failed to find proof to " ++ (show expr))
findModusPonens expr list =
    case proofStatement $ head list of
        Implication a b ->
            if (b == expr) then case findProof a list of
                Just p -> ModusPonens p (head list)
                Nothing -> cont
            else cont
        _ -> cont
        where cont =
                case findProof (Implication (proofStatement $ head list) expr) list of
                    Just p -> ModusPonens (head list) p
                    Nothing -> findModusPonens expr (tail list)


getProof :: [Expression] -> [String] -> [ProofTree] -> ProofTree
getProof hypoList [] prevProofs = head prevProofs
getProof hypoList lines prevProofs =
    let expr = parse $ head lines in
    if isAxiom expr then
        getProof hypoList (tail lines) ((Axiom expr) : prevProofs)
    else if expr `elem` hypoList then
        getProof hypoList (tail lines) ((Hypothesis expr) : prevProofs)
    else getProof hypoList (tail lines) ((findModusPonens expr prevProofs) : prevProofs)

do_main l =
    let header = parseProofHeader (splitToTokens $ head l) in
    let proof = 
            case header of
                ProofHeader hypolist expr -> Proof hypolist (getProof hypolist (tail l) []) in
    (show (deduction proof)) ++ "\n"

main = interact (do_main . lines)
