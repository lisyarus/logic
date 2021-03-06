all: Deduction Completeness

Deduction: Expression.hs Deduction.hs DeductionMain.hs
	ghc -Wall --make DeductionMain.hs -o Deduction

Completeness: Expression.hs Completeness.hs CompletenessMain.hs
	ghc -Wall --make CompletenessMain.hs -o Completeness

clean:
	rm *.hi
	rm *.o
	rm Deduction
	rm Completeness
