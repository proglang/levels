.PHONY: run clean cleanrun

run:
	./runagdatex
	pdflatex main

clean:
	$(RM) -f main.aux main.log main.out main.ptb texput.log

cleanrun: clean run
