
all: cfa

cfa: *.hs
	cabal install

clean:
	rm *.o cfa *.hi
