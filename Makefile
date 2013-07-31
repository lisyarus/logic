Deduction: Expression.hs Deduction.hs Main.hs
	ghc --make Main.hs -o Deduction

clean:
	rm *.hi
	rm *.o
	rm Deduction
