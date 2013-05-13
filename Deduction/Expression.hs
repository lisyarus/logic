module Expression where

data Expression = Variable String
                | Negation Expression
                | Implication Expression Expression
                | Conjunction Expression Expression
                | Disjunction Expression Expression
                deriving(Eq)

instance Show(Expression) where
    show (Variable s) = s
    show (Negation e) = "¬" ++ (show e)
    show (Implication e1 e2) = (show e1) ++ "→" ++ (show e2)
    show (Conjunction e1 e2) = "(" ++ (show e1) ++ "∧" ++ (show e2) ++ ")"
    show (Disjunction e1 e2) = "(" ++ (show e1) ++ "∨" ++ (show e2) ++ ")"

data ProofTree =  Axiom Expression
                | Hypothesis Expression
                | ModusPonens ProofTree ProofTree -- (ModusPonens A B) means a proof of C from proofs of A and B = (A -> C)

proofStatement :: ProofTree -> Expression
proofStatement (Axiom ax) = ax
proofStatement (Hypothesis hypo) = hypo
proofStatement (ModusPonens a ac) =
    let ast = proofStatement a
        acst = proofStatement ac in
    case acst of
        Implication b c -> if (ast == b) then c else undefined
        _ -> undefined

instance Show(ProofTree) where
    show (Axiom ax) = (show ax) ++ " (axiom)"
    show (Hypothesis hypo) = (show hypo) ++ " (hypothesis)"
    show p@(ModusPonens a ac) = (show a) ++ "\n" ++ (show ac) ++ "\n" ++ (show (proofStatement p))


data Proof = Proof [Expression] ProofTree -- Hypothesis list and the proof

instance Show(Proof) where
    show (Proof hypothesis proofTree) = (show hypothesis) ++ " ⊢ " ++ (show (proofStatement proofTree)) ++ "\n" ++ (show proofTree)
