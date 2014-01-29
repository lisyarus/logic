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

splitToTokensImpl :: String -> TokenList
splitToTokensImpl [] = [""]
splitToTokensImpl (c:tail) =
    if (isAlphaNum c) then addToLast c (splitToTokensImpl tail) else
    if (isSpace c) then ensureHasEmpty (splitToTokensImpl tail) else
    if (c == '-') then case (splitToTokensImpl tail) of
        ("":">":tail1) -> "":"->":tail1
        "":tail1 -> "":"-":tail1 else
    if (c == ':') then case (splitToTokensImpl tail) of
        ("":"-":tail1) -> "":":-":tail1
        "":tail1 -> "":":":tail1 else
    putAnother c (ensureHasEmpty (splitToTokensImpl tail))

splitToTokens string =
    case splitToTokensImpl string of
        "":tail -> tail
        tail -> tail

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
    parseTerm ("!":name@(c:_):tail) | (isAlphaNum c) = ParseState (Negation (Variable name)) tail
    parseTerm ("!":tail) = let res = parseImplication tail in ParseState (Negation (stateExpression res)) (stateTokenList res)
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
        Implication b c -> if (aSt == b) then c else badModusPonens a ac
        _ -> badModusPonens a ac
    where
        badModusPonens a ac = error ("bad modus ponens from " ++ (show $ proofStatement a) ++ " and " ++ (show $ proofStatement ac))

getProofTree proof =
   case proof of
      Proof _ tree -> tree

showProof :: ProofTree -> Int -> (String, Int)
showProof (Axiom ax) index = ((show index) ++ ".  " ++ (show ax) ++ " (axiom)", index + 1)
showProof (Hypothesis hypo) index = ((show index) ++ ".  " ++ (show hypo) ++ " (hypothesis)", index + 1)
showProof p@(ModusPonens a ac) index = 
   let (aproof, aindex) = (showProof a index) in
   let (acproof, acindex) = (showProof ac aindex) in
   (aproof ++ "\n" ++ acproof ++ "\n" ++ (show acindex) ++ ".  " ++ (show (proofStatement p)) ++ " (modus ponens " ++ (show (aindex - 1)) ++ " and " ++ (show (acindex - 1)) ++ ")", acindex + 1)

instance Show(ProofTree) where
   show p = let (str, _) = showProof p 1 in str


data Proof = Proof [Expression] ProofTree -- Hypothesis list and the proof

instance Show(Proof) where
    show (Proof hypothesis proofTree) = (showList hypothesis) ++ " :- " ++ (show (proofStatement proofTree)) ++ "\n" ++ (show proofTree)
        where
            showList (head1:head2:tail) = (show head1) ++ ", " ++ show(head2:tail)
            showList [head] = (show head)
            showList [] = ""

isAxiom :: Expression -> Bool
isAxiom (Implication (Implication a1 b1) (Implication (Implication a2 (Implication b2 c1)) (Implication a3 c2))) = (a1 == a2) && (a2 == a3) && (b1 == b2) && (c1 == c2)
isAxiom (Implication a1 (Implication b1 (Conjunction a2 b2))) = (a1 == a2) && (b1 == b2)
isAxiom (Implication (Conjunction a1 b1) ab) = (a1 == ab) || (b1 == ab)
isAxiom (Implication ab (Disjunction a1 b1)) = (a1 == ab) || (b1 == ab)
isAxiom (Implication (Implication a1 c1) (Implication (Implication b1 c2) (Implication (Disjunction a2 b2) c3))) = (a1 == a2) && (b1 == b2) && (c1 == c2) && (c2 == c3)
isAxiom (Implication (Implication a1 b1) (Implication (Implication a2 (Negation b2)) (Negation a3))) = (a1 == a2) && (a2 == a3) && (b1 == b2)
isAxiom (Implication (Negation (Negation a1)) a2) = (a1 == a2)
isAxiom (Implication a1 (Implication b1 a2)) = (a1 == a2)
isAxiom _ = False

axiom1 a b = Axiom $ Implication a $ Implication b a
axiom6 a b = Axiom $ Implication a $ Disjunction a b
axiom7 a b = Axiom $ Implication b $ Disjunction a b
axiom8 a b c = Axiom $ Implication (Implication a c) $ Implication (Implication b c) $ Implication (Disjunction a b) c
axiom9 a b = Axiom $ Implication (Implication a b) (Implication (Implication a (Negation b)) (Negation a))
axiom10 a = Axiom $ Implication (Negation $ Negation a) a

-- proves that a -> b (assuming b is true)
truthImplication a b = ModusPonens (Hypothesis b) (axiom1 b a)

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
