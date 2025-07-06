all:
	rocq makefile -f _CoqProject -o Makefile.rocq $(shell find . -regex '.*\.v')
	make -f Makefile.rocq

clean:
	rm -f Makefile.rocq Makefile.rocq.conf .Makefile.rocq.d
	find . -regex '.*\.vo' -delete
	find . -regex '.*\.vok' -delete
	find . -regex '.*\.vos' -delete
	find . -regex '.*\.glob' -delete
	find . -regex '.*\.aux' -delete
	find . -regex '.*\.cache' -delete

.PHONY: all clean
