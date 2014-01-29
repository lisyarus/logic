module Deduction where

import Expression

removeHypothesis :: Expression -> ProofTree -> ProofTree
removeHypothesis hypo (Axiom ax) = ModusPonens (Axiom ax) (Axiom (Implication ax (Implication hypo ax)))
removeHypothesis hypo (Hypothesis h) =
    if (h == hypo) then
        let temp1 = Implication h (Implication h h) -- (A -> A -> A)
            temp2 = Implication h (Implication (Implication h h) h) in -- (A -> (A -> A) -> A)
        ModusPonens
            (Axiom temp2)
            (ModusPonens
                (Axiom temp1)
                (Axiom (Implication temp1 (Implication temp2 (Implication h h))))
            )
    else
        ModusPonens (Hypothesis h) (Axiom (Implication h (Implication hypo h)))
removeHypothesis hypo (ModusPonens a ac) =
    let ha = removeHypothesis hypo a -- proof of H -> A
        hac = removeHypothesis hypo ac -- proof of H -> A -> C
        haSt = proofStatement ha -- H -> A
        hacSt = proofStatement hac -- H -> A -> C
        h = case haSt of Implication hh _ -> hh
        c = case hacSt of Implication _ (Implication _ cc) -> cc in
    ModusPonens hac (ModusPonens
        ha
        (Axiom (Implication haSt (Implication hacSt (Implication h c))))
    )

deduction :: Proof -> Proof
deduction p@(Proof [] _) = p
-- deduction (Proof (hypo : hypoTail) tree) = deduction (Proof hypoTail (simplifyProof hypoTail (removeHypothesis hypo tree)))
deduction (Proof (hypo : hypoTail) tree) = 
   case deduction (Proof hypoTail tree) of
      Proof _ tree -> Proof [] (simplifyProof [] (removeHypothesis hypo tree)) 

selfImplicationProof :: Expression -> ProofTree
selfImplicationProof expr =
   case deduction (Proof [expr] (Hypothesis expr)) of
      Proof _ tree -> tree
