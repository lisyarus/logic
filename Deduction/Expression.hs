module Expression where

import Data.Char

data Expression = Variable String
                | Negation Expression
                | Implication Expression Expression
                | Conjunction Expression Expression
                | Disjunction Expression Expression
                deriving(Eq)

instance Show(Expression) where
    show (Variable s) = s
    show (Negation e) = "!" ++ (show e)
    --show (Implication e1@(Implication _ _) e2) = "(" ++ (show e1) ++ ") -> " ++ (show e2)
    show (Implication e1 e2) = "(" ++ (show e1) ++ " -> " ++ (show e2) ++ ")"
    show (Conjunction e1 e2) = "(" ++ (show e1) ++ " & " ++ (show e2) ++ ")"
    show (Disjunction e1 e2) = "(" ++ (show e1) ++ " | " ++ (show e2) ++ ")"

type TokenList = [String]

ensureHasEmpty :: TokenList -> TokenList
ensureHasEmpty ("":tail) = "":tail
ensureHasEmpty list = "":list

addToLast :: Char -> TokenList -> TokenList
addToLast c (head:tail) = (c:head):tail

putAnother :: Char -> TokenList -> TokenList
putAnother c list = "" : (addToLast c list)

splitToTokens :: String -> TokenList
splitToTokens [] = [""]
splitToTokens (c:tail) =
    if (isAlphaNum c) then addToLast c (splitToTokens tail) else
    if (isSpace c) then ensureHasEmpty (splitToTokens tail) else
    if (c == '-') then case (splitToTokens tail) of
        ("":">":tail1) -> "":"->":tail1
        "":tail1 -> "":"-":tail1 else
    if (c == ':') then case (splitToTokens tail) of
        ("":"-":tail1) -> "":":-":tail1
        "":tail1 -> "":":":tail1 else
    putAnother c (ensureHasEmpty (splitToTokens tail))

data ParseState = ParseState Expression TokenList

stateExpression (ParseState expr _) = expr
stateTokenList (ParseState _ tokenList) = tokenList

parseImplication :: TokenList -> ParseState
parseImplication tokenList =
    let res = parseDisjunction tokenList in
    case res of
        ParseState expr ("->":tokenTail) -> let res2 = parseImplication tokenTail in ParseState (Implication expr (stateExpression res2)) (stateTokenList res2)
        ParseState expr tail -> ParseState expr tail
    where
    parseTerm :: TokenList -> ParseState
    parseTerm ((name@(c:nameTail)):tail) | (isAlphaNum c) = ParseState (Variable name) tail
    parseTerm ("(":tail) = case res of
        ParseState expr (")":tail1) -> ParseState expr tail1
        where res = (parseImplication tail)
    parseConjunction :: TokenList -> ParseState
    parseConjunction tokenList =
        let res = parseTerm tokenList in
        case res of
            ParseState expr ("&":tokenTail) -> let res2 = parseConjunction tokenTail in ParseState (Conjunction expr (stateExpression res2)) (stateTokenList res2)
            ParseState expr tail -> ParseState expr tail
    parseDisjunction :: TokenList -> ParseState
    parseDisjunction tokenList =
        let res = parseConjunction tokenList in
        case res of
            ParseState expr ("|":tokenTail) -> let res2 = parseDisjunction tokenTail in ParseState (Disjunction expr (stateExpression res2)) (stateTokenList res2)
            ParseState expr tail -> ParseState expr tail

parse string = case (splitToTokens string) of
    "":tokenTail -> stateExpression (parseImplication tokenTail)
    tokenList -> stateExpression (parseImplication tokenList)

data ProofTree =  Axiom Expression
                | Hypothesis Expression
                | ModusPonens ProofTree ProofTree -- (ModusPonens A B) means a proof of C from proofs of A and B = (A -> C)

proofStatement :: ProofTree -> Expression
proofStatement (Axiom ax) = ax
proofStatement (Hypothesis hypo) = hypo
proofStatement (ModusPonens a ac) =
    let aSt = proofStatement a
        acSt = proofStatement ac in
    case acSt of
        Implication b c -> if (aSt == b) then c else undefined
        _ -> undefined

instance Show(ProofTree) where
    show (Axiom ax) = (show ax) ++ " (axiom)"
    show (Hypothesis hypo) = (show hypo) ++ " (hypothesis)"
    show p@(ModusPonens a ac) = (show a) ++ "\n" ++ (show ac) ++ "\n" ++ (show (proofStatement p)) ++ " (modus ponens)"


data Proof = Proof [Expression] ProofTree -- Hypothesis list and the proof

instance Show(Proof) where
    show (Proof hypothesis proofTree) = (showList hypothesis) ++ " :- " ++ (show (proofStatement proofTree)) ++ "\n" ++ (show proofTree)
        where
            showList (head1:head2:tail) = (show head1) ++ ", " ++ show(head2:tail)
            showList [head] = (show head)
            showList [] = ""

isAxiom :: Expression -> Bool
isAxiom (Implication (Implication a1 b1) (Implication (Implication a2 (Implication b2 c1)) (Implication a3 c2))) = (a1 == a2) && (a2 == a3) && (b1 == b2) && (c1 == c2)
isAxiom (Implication a1 (Implication b1 (Conjunction a2 b2))) = (a1 == a2) && (b1 == a2)
isAxiom (Implication (Conjunction a1 b1) ab) = (a1 == ab) || (b1 == ab)
isAxiom (Implication ab (Disjunction a1 b1)) = (a1 == ab) || (b1 == ab)
isAxiom (Implication (Implication a1 c1) (Implication (Implication b1 c2) (Implication (Disjunction a2 b2) c3))) = (a1 == a2) && (b1 == b2) && (c1 == c2) && (c2 == c3)
isAxiom (Implication (Implication a1 b1) (Implication (Implication a2 (Negation b2)) (Negation a3))) = (a1 == a2) && (a2 == a3) && (b1 == b2)
isAxiom (Implication (Negation (Negation a1)) a2) = (a1 == a2)
isAxiom (Implication a1 (Implication b1 a2)) = (a1 == a2)
isAxiom _ = False

simplifyProof :: [Expression] -> ProofTree -> ProofTree
simplifyProof hypoList proofTree =
    let statement = proofStatement proofTree in
    if (isAxiom statement) then
        (Axiom statement)
    else if (elem statement hypoList) then
        (Hypothesis statement)
    else
        case proofTree of
            (ModusPonens a ac) -> ModusPonens (simplifyProof hypoList a) (simplifyProof hypoList ac)
            x -> x
