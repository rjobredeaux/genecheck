# -*- Makefile -*-

MAIN_SOURCES = utils.ml matrix.ml trivialPVS.ml trivialPVSParser.ml trivialPVSLexer.ml ellipsoid_pvs.ml
PLUGIN_EXTRA_OPT= posdef.cmxa
VERBOSEMAKE=yes
FRAMAC_SHARE =$(shell frama-c -print-path )
FRAMAC_LIBDIR =$(shell frama-c -print-libpath )
PLUGIN_NAME = EllipsoidPVS
PLUGIN_CMO = $(MAIN_SOURCES:.ml=)

posdef.cmi:
	gcc -c posdef_stubs.c -I /usr/local/lib/ocaml/ -fpic
	ar rcs libposdef_stubs.a posdef_stubs.o
	ocamlopt -a  posdef.mli posdef.ml -cclib -lposdef_stubs -o posdef.cmxa

matrix.cmo: matrix.cmi
trivialPVSParser.cmo: trivialPVSParser.cmi
clean_clib:
	rm -f posdef.a libposdef_stubs.a trivialPVSParser.output


clean:: clean_clib

include $(FRAMAC_SHARE)/Makefile.dynamic

