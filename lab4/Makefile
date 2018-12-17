# Makefile for PLT lab 4

lab4: lab4.hs Interpreter.hs Fun/Test
	ghc --make lab4.hs -o lab4

Fun/Test.hs Fun/Lex.x Fun/Layout.hs Fun/Par.y : Fun.cf
	bnfc --haskell -d $<

Fun/Par.hs: Fun/Par.y
	happy -gcai $<

Fun/Lex.hs: Fun/Lex.x
	alex -g $<

Fun/Test: Fun/Test.hs Fun/Par.hs Fun/Lex.hs
	ghc --make $< -o $@

clean:
	-rm -f Fun/*.log Fun/*.aux Fun/*.hi Fun/*.o Fun/*.dvi

distclean: clean
	-rm -f Fun/Doc.* Fun/Lex.* Fun/Par.* Fun/Layout.* Fun/Skel.* Fun/Print.* Fun/Test.* Fun/Abs.* Fun/Test Fun/ErrM.* Fun/SharedString.* Fun/ComposOp.* Fun/Fun.dtd Fun/XML.*
	-rmdir -p Fun/

# EOF
