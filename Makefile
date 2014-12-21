all: avl

avl: AVL.hs
	ghc $(FLAGS) AVL.hs

clean:
	rm *.o
	rm *.hi
