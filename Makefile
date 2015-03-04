
all: cfa

cfa: *.hs
	ghc -O3 Main.hs -o pdcfa

clean:
	rm *.o cfa *.hi
