Deduction: Expression.hs Deduction.hs DeductionMain.hs
	ghc --make DeductionMain.hs -o Deduction

clean:
	rm *.hi
	rm *.o
	rm Deduction
